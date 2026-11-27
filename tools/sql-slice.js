/* Dependency projection + proven-singleton relation pruning, to a fixed point.
 * Never assumes physical table uniqueness, foreign keys or sample-data cardinality.
 * Unknown syntax/functions and DISTINCT/set grain remain conservative boundaries. */
const SQLSlice=(()=>{
  const scalarFns=new Set('IFNULL NULLIF COALESCE NVL NVL2 IF IFF ABS ROUND TRUNC TRUNCATE CEIL CEILING FLOOR MOD POWER SQRT SIGN LEN LENGTH CHAR_LENGTH LOWER UPPER TRIM LTRIM RTRIM SUBSTR SUBSTRING LEFT RIGHT REPLACE CONCAT CONCAT_WS TO_CHAR TO_DATE TO_NUMBER CAST CONVERT ADD_MONTHS DATEADD DATEDIFF EXTRACT DATE_FORMAT STRFTIME ISNULL IN OVER FILTER PARTITION MONTH YEAR DAY SUM AVG COUNT MIN MAX LISTAGG STRING_AGG ARRAY_AGG STDDEV VARIANCE'.split(' '));
  const unknownFunction=(m,q)=>[...q.fields,...Object.values(q.clauseRanges).map(range=>({range,scalar:[]}))].some(f=>m.tokens.slice(...f.range).some((t,n)=>{const i=f.range[0]+n;return ['word','id'].includes(t.kind)&&m.tokens[i+1]?.kind==='symbol'&&m.tokens[i+1]?.value==='('&&!/^(ELSE|THEN|WHEN|AND|OR|NOT|AS|SELECT|WHERE|BY|DISTINCT)$/i.test(t.value)&&(!scalarFns.has(t.value.toUpperCase())||m.tokens[i-1]?.value==='.'||t.kind==='id')&&!f.scalar.some(s=>i>=s.start&&i<=s.end);}));
  const quoted=name=>'"'+String(name).replace(/"/g,'""')+'"';
  function expandWildcards(sql,metadata,parser){
    const expanded=[];
    for(let pass=0;pass<32;pass++){
      const m=parser.parse(sql,metadata,{conditionQueries:true}),edits=[];
      for(const q of m.scopes)for(const f of q.fields){
        const [a,b]=f.range,t=m.tokens,qualifier=b-a===3&&t[a+1]?.value==='.'&&t[a+2]?.value==='*'?t[a].value:null;
        const star=qualifier!==null||b-a===1&&t[a]?.value==='*';if(!star)continue;
        const candidates=q.sources.filter(s=>!qualifier||s.alias.toUpperCase()===qualifier.toUpperCase()||s.name.toUpperCase()===qualifier.toUpperCase());
        // Expanding an unqualified star across joins can create duplicate output
        // names and change downstream name resolution. Only expand a single source.
        if(candidates.length!==1)continue;
        const source=candidates[0];let columns;
        if(source.query){
          const child=m.byId[source.query];if(!child||child.fields.some(x=>x.expr==='*'||/\.\s*\*$/.test(x.expr)))continue;
          columns=child.fields.map(x=>x.alias);
        }else columns=metadata?.(source);
        if(!Array.isArray(columns)||!columns.length)continue;
        const expressions=columns.map(c=>source.alias+'.'+quoted(c)).join(', ');
        edits.push({a:t[f.outputRange[0]].start,b:t[f.outputRange[1]-1].end,text:expressions});
      }
      if(!edits.length)return {sql,expanded,model:m};
      edits.sort((a,b)=>b.a-a.a);for(const e of edits){sql=sql.slice(0,e.a)+e.text+sql.slice(e.b);expanded.push(e.text);}
    }
    return {sql,expanded,error:'通配符展开超过安全迭代上限'};
  }
  function project(model,fieldId,metadata){
    const m=model,f=m.fields[fieldId];
    if(!f||f.scope!==m.root.id)return {ok:false,reason:'请选择一个最终输出字段。'};
    if(m.warnings.length)return {ok:false,reason:'此查询包含尚未完整支持的语法，保留原 SQL，不生成可能改变结果的简化版。',warnings:m.warnings};
    const tokens=m.tokens,sql=m.sql,needed=new Map(),active=new Set(),work=[],keptBarriers=new Set();
    if(tokens.some(t=>t.kind==='word'&&/^(INTO|UPDATE|DELETE|INSERT|MERGE|CALL|EXEC|NEXTVAL)$/i.test(t.value)))return {ok:false,reason:'包含写入、锁定或序列操作，不生成和执行单字段 SQL。'};
    if(tokens.some(t=>t.kind==='symbol'&&(t.value==='@'||t.value==='{'||t.value==='}')))return {ok:false,reason:'包含未替换的模板或变量语法，请先提供可独立执行的 SELECT。'};
    if(m.scopes.some(q=>q.joins.some(j=>/NATURAL/i.test(j.type))))return {ok:false,reason:'NATURAL JOIN 依赖完整同名字段集合，暂不裁剪。请先改成明确的 ON / USING 条件。'};
    // Unknown functions can be user-defined aggregates. Never infer row cardinality
    // from an incomplete aggregate-name list. Keep their complete projection.
    const namedScopes=new Set(m.scopes.flatMap(q=>q.definitions.filter(d=>d.names.length).flatMap(d=>m.scopes.filter(s=>s.range[0]===d.a&&s.range[1]===d.b).map(s=>s.id))));
    const ordinalClause=q=>['GROUP','ORDER'].some(k=>{
      const range=q.clauseRanges[k];if(!range)return false;
      const groups=[[]];for(let i=range[0];i<range[1];i++){
        if(tokens[i].kind==='symbol'&&tokens[i].value==='('){groups.at(-1).push('EXPRESSION');i=tokens[i].pair;}
        else if(tokens[i].kind==='symbol'&&tokens[i].value===',')groups.push([]);else groups.at(-1).push(tokens[i].raw);
      }
      return groups.some(g=>/^\d+(?:\s+(?:ASC|DESC))?(?:\s+NULLS\s+(?:FIRST|LAST))?$/i.test(g.join(' ')))||k==='GROUP'&&/\b(?:ROLLUP|CUBE|GROUPING)\b/i.test(q.clauses[k]);
    });
    const barrier=q=>!!(namedScopes.has(q.id)||unknownFunction(m,q)||q.branches||q.distinct==='DISTINCT'||ordinalClause(q));
    const want=(id)=>{const field=m.fields[id];if(!field)return;let set=needed.get(field.scope);if(!set)needed.set(field.scope,set=new Set());if(!set.has(id)){set.add(id);work.push({field});}};
    const use=q=>{if(!q||active.has(q.id))return;active.add(q.id);work.push({query:q});if(barrier(q)){keptBarriers.add(q.id);q.fields.forEach(x=>want(x.id));}};
    const deps=(q,ds)=>ds.forEach(d=>{
      if(d.kind==='field'){const x=m.fields[d.id];use(m.byId[x?.scope]);want(d.id);}
      if(d.kind==='unknown'){
        // Unknown qualification/metadata is never grounds to drop a source column.
        q.sources.forEach(s=>{if(s.query)m.byId[s.query].fields.forEach(x=>want(x.id));});
      }
    });
    use(m.root);want(fieldId);
    const drain=()=>{while(work.length){const {field,query:q}=work.shift();
      if(field){const scope=m.byId[field.scope];deps(scope,field.deps);field.scalar.forEach(s=>use(m.byId[s.query]));}
      if(q){q.sources.forEach(s=>{if(s.query)use(m.byId[s.query]);});(q.branches||[]).forEach(use);
      Object.values(q.clauseRanges).forEach(r=>deps(q,m.references(q.id,r)));
      // A predicate subquery can change which rows survive even when its
      // projected value is not selected. Keep its full query grain and inputs.
      (q.conditionQueries||[]).forEach(s=>{const sub=m.byId[s.query];use(sub);sub?.fields.forEach(x=>want(x.id));});
        q.joins.forEach(j=>{if(j.range)deps(q,m.references(q.id,j.range));});
      }
    }};
    drain();
    // Removing the last aggregate from an ungrouped SELECT changes its grain,
    // especially on empty inputs. Keep one aggregate witness and project outside.
    active.forEach(id=>{const q=m.byId[id];if(!q.clauses.GROUP&&q.fields.some(x=>x.groupAggregate)&&!q.fields.some(x=>needed.get(id)?.has(x.id)&&x.groupAggregate))want(q.fields.find(x=>x.groupAggregate).id);});drain();
    // FROM-only subqueries must still produce their original rows. A retained
    // first projection also preserves its errors/volatile expression semantics.
    active.forEach(id=>{const q=m.byId[id];if(!needed.get(id)?.size&&q.fields[0])want(q.fields[0].id);});drain();
    // Volatile functions and pseudo-columns only make a field slice unsafe
    // when they participate in the selected field's dependency graph. The
    // old whole-statement scan treated ordinary columns named UUID (and
    // unrelated subqueries containing ROWNUM) as volatile, which rejected
    // safe slices from otherwise valid SQL. Inspect only retained fields and
    // row-shaping clauses after dependency discovery. Function names are
    // recognized only when followed by `(`, while dialect pseudo-columns are
    // recognized as identifiers.
    const volatileFunctions=new Set('RANDOM RAND NEWID UUID SYSDATE SYSTIMESTAMP CURRENT_TIMESTAMP CURRENT_DATE CURRENT_TIME GETDATE NOW'.split(' '));
    const bareVolatileKeywords=new Set('SYSDATE SYSTIMESTAMP CURRENT_TIMESTAMP CURRENT_DATE CURRENT_TIME'.split(' '));
    const volatilePseudoColumns=new Set('NEXTVAL CURRVAL ROWNUM'.split(' '));
    const volatileInRange=range=>{
      if(!range)return null;
      for(let i=range[0];i<range[1];i++){
        const token=tokens[i];if(token?.kind!=='word')continue;
        if(volatileFunctions.has(token.u)&&tokens[i+1]?.kind==='symbol'&&tokens[i+1]?.value==='(')return token.value;
        if(bareVolatileKeywords.has(token.u))return token.value;
        if(volatilePseudoColumns.has(token.u))return token.value;
      }
      return null;
    };
    const volatileRanges=[];
    active.forEach(id=>{
      const q=m.byId[id],kept=needed.get(id);if(!kept?.size)return;
      q.fields.forEach(x=>{if(kept.has(x.id))volatileRanges.push(x.range);});
      Object.values(q.clauseRanges).forEach(r=>volatileRanges.push(r));
      q.joins.forEach(j=>{if(j.range)volatileRanges.push(j.range);});
    });
    for(const range of volatileRanges){const hit=volatileInRange(range);if(hit)return {ok:false,reason:'所选字段依赖随机值、当前时间、序列或依赖执行顺序的伪列（'+hit+'），无法稳定比较两次执行；请保留原 SQL。'};}
    const removed=[],edits=[];
    const charRange=r=>[tokens[r[0]].start,tokens[r[1]-1].end];
    const add=(r,replacement)=>{const [a,b]=charRange(r);edits.push({a,b,replacement});};
    const slice=r=>{const [a,b]=charRange(r);return apply(a,b);};
    function apply(a,b){let pos=a,out='';const inside=edits.filter(e=>e.a>=a&&e.b<=b).sort((x,y)=>x.a-y.a||y.b-x.b);
      for(const e of inside){if(e.a<pos)continue;out+=sql.slice(pos,e.a)+e.replacement;pos=e.b;}return out+sql.slice(pos,b);}
    // Inner edits first: replacing a projection or WITH incorporates its children.
    [...m.scopes].sort((a,b)=>(a.range[1]-a.range[0])-(b.range[1]-b.range[0])).forEach(q=>{
      if(!active.has(q.id))return;
      if(q.projection&&!barrier(q)){
        const fields=q.fields.filter(x=>needed.get(q.id)?.has(x.id));
        if(fields.length&&fields.length<q.fields.length){
          const text=fields.map(x=>slice(x.outputRange)).join(',\n  ');
          const a=tokens[q.projection[0]].start,b=tokens[q.projection[1]]?.start??sql.length;
          edits.push({a,b,replacement:text+'\n'});q.fields.filter(x=>!needed.get(q.id)?.has(x.id)).forEach(x=>removed.push(q.label+'.'+x.alias));
        }
      }
      if(q.withRange){
        const defs=q.definitions.filter(d=>m.scopes.some(s=>active.has(s.id)&&s.range[0]===d.a&&s.range[1]===d.b));
        if(defs.length<q.definitions.length){add(q.withRange,defs.length?'WITH '+defs.map(d=>slice(d.range)).join(',\n')+'\n':'');q.definitions.filter(d=>!defs.includes(d)).forEach(d=>removed.push('CTE '+d.name));}
      }
    });
    let result=apply(0,sql.length).trim().replace(/;\s*$/,'');
    const rootKept=m.root.fields.filter(x=>needed.get(m.root.id)?.has(x.id));
    if(rootKept.length>1){
      // Do not introduce a derived-table ORDER BY that SQL Server rejects.
      // With no connection dialect, declining is safer than inventing OFFSET,
      // dropping ordering, or moving ordinal/hidden sort expressions outside.
      const ordered=m.root.branches?.at(-1)||m.root;
      if(ordered.clauses.ORDER&&!['TOP','LIMIT','OFFSET','FETCH'].some(k=>ordered.clauses[k]!==undefined))return {ok:false,reason:'需要保留内部多列及 ORDER BY，但无行数限制的排序在部分数据库中不能包装为子查询。请保留原 SQL；不会删除排序或擅自添加方言语法。'};
      if(m.root.fields.filter(x=>x.alias.toUpperCase()===f.alias.toUpperCase()).length!==1)return {ok:false,reason:'输出存在重名字段，请设置唯一的 AS 别名后再生成单字段 SQL。'};
      // An outer projection leaves DISTINCT/group/set cardinality untouched.
      if(!f.aliasSQL||f.aliasSQL!==f.alias&&!/^[["`]/.test(f.aliasSQL))return {ok:false,reason:'此字段没有可引用的输出别名。请先给字段设置 AS 别名，再生成单字段 SQL。'};
      // SQL Server requires WITH before the statement, not inside a derived
      // table. Keep the original CTE prefix at statement level in every dialect.
      const reader=typeof SQLLogic!=='undefined'?SQLLogic:require('./sql-logic.js');
      const rm=reader.parse(result,metadata,{conditionQueries:true}),wr=rm.root.withRange,cut=wr?rm.tokens[wr[1]].start:0;
      result=result.slice(0,cut)+'SELECT __sql_field.'+f.aliasSQL+'\nFROM (\n'+result.slice(cut)+'\n) __sql_field';
    }
    return {ok:true,sql:result,field:f.alias,removed,retainedScopes:[...active],barriers:[...keptBarriers],
      retainedJoins:[...active].reduce((n,id)=>n+m.byId[id].joins.length,0),
      status:'未执行数据库比对',note:'逐层裁剪无关字段、标量子查询和 CTE；仅在能证明行数不变时移除无关关联。保留影响结果的筛选、分组、去重和排序。'};
  }
  function pruneRelations(m){
    const edits=[],removed=[],t=m.tokens,truth=j=>!j.kind||j.kind==='ON'&&/^(?:1=1|TRUE)$/i.test(j.condition.replace(/[\s()]/g,''));
    const memo=new Map();
    function one(q,seen=new Set()){
      if(!q||seen.has(q.id))return false;if(memo.has(q.id))return memo.get(q.id);seen=new Set([...seen,q.id]);
      if(q.branches||q.warnings.length||unknownFunction(m,q)||['GROUP','HAVING','QUALIFY','LIMIT','OFFSET','FETCH','TOP','CONNECT','START'].some(k=>q.clauses[k]!==undefined))return false;
      let yes=q.fields.some(f=>f.groupAggregate);
      if(!yes&&!q.clauses.WHERE)yes=q.sources.every(s=>s.query&&one(m.byId[s.query],seen))&&q.joins.every(j=>/LEFT/.test(j.type)||truth(j));
      memo.set(q.id,yes);return yes;
    }
    const raw=r=>m.sql.slice(t[r[0]].start,t[r[1]-1].end);
    for(const q of m.scopes){
      if(!q.fromRange||q.branches||q.sources.length<2||q.joins.some(j=>/RIGHT|FULL|NATURAL/.test(j.type)))continue;
      const refs=r=>{const ds=m.references(q.id,r),aliases=new Set();
        for(const d of ds){if(d.kind==='unknown')return new Set(q.sources.map(s=>s.alias));if(d.kind==='field'){const f=m.fields[d.id];q.sources.filter(s=>s.query===f?.scope).forEach(s=>aliases.add(s.alias));}else q.sources.filter(s=>s.id===d.source).forEach(s=>aliases.add(s.alias));}
        return aliases;
      };
      const used=new Set();[...q.fields.map(f=>f.range),...Object.values(q.clauseRanges)].forEach(r=>refs(r).forEach(a=>used.add(a)));
      // If every input has exactly one row and every ON is true, an unused
      // driving singleton can be replaced with a used singleton (LEFT included).
      const allOne=q.sources.every(s=>s.query&&one(m.byId[s.query]))&&q.joins.every(truth);
      if(allOne){
        const keep=q.sources.filter(s=>used.has(s.alias));if(!keep.length)keep.push(q.sources[0]);
        if(keep.length<q.sources.length){
          const replacement=keep.map((s,i)=>(i?'\nCROSS JOIN ':'')+raw(s.range)).join('');
          edits.push({a:t[q.fromRange[0]].start,b:t[q.fromRange[1]-1].end,text:replacement+'\n'});
          q.sources.filter(s=>!keep.includes(s)).forEach(s=>removed.push(q.label+' 关联 '+s.alias));
        }continue;
      }
      // Walk backwards: a kept later ON may require an earlier right relation.
      const drops=[];
      for(let i=q.joins.length-1;i>=0;i--){const j=q.joins[i],s=q.sources[i+1];
        if(!used.has(s.alias)&&s.query&&one(m.byId[s.query])&&(/LEFT/.test(j.type)||truth(j))){drops.push(j);removed.push(q.label+' 关联 '+s.alias);}
        else if(j.range)refs(j.range).forEach(a=>used.add(a));
      }
      drops.forEach(j=>edits.push({a:t[j.fullRange[0]].start,b:t[j.fullRange[1]-1].end,text:'\n'}));
    }
    // Do not let an outer replacement overwrite a nested relation edit. They
    // are revisited on the next pass; apply only innermost edits this pass.
    const inner=edits.filter(e=>!edits.some(x=>x!==e&&x.a>=e.a&&x.b<=e.b));
    let out=m.sql;inner.sort((a,b)=>b.a-a.a).forEach(e=>out=out.slice(0,e.a)+e.text+out.slice(e.b));return {sql:out,removed};
  }
  function generate(model,fieldId,metadata){
    const parser=typeof SQLLogic!=='undefined'?SQLLogic:require('./sql-logic.js');
    let sourceModel=model;
    if(metadata){
      try{const expanded=expandWildcards(model.sql,metadata,parser);if(expanded.error)return {ok:false,reason:expanded.error};
        sourceModel=parser.parse(expanded.sql,metadata,{conditionQueries:true});
      }catch(e){return {ok:false,reason:'無法使用資料字典展開 SELECT *：'+e.message};}
    }
    model=sourceModel;
    const first=project(model,fieldId,metadata);if(!first.ok)return first;
    const removed=[...first.removed];let result=first,current=first.sql,stable=false;
    // Bound work on pathological input. Never advertise a partial transformation
    // when a reparsing/dependency failure occurs.
    try{for(let pass=0;pass<32;pass++){
      let m=parser.parse(current,metadata,{conditionQueries:true}),relations=pruneRelations(m);removed.push(...relations.removed);
      m=parser.parse(relations.sql,metadata,{conditionQueries:true});const next=project(m,m.root.fields[0].id,metadata);if(!next.ok)return next;
      removed.push(...next.removed);result=next;if(next.sql===current){stable=true;break;}current=next.sql;
    }
    if(!stable)return {ok:false,reason:'裁剪未能在限定轮次内稳定，请保留原 SQL。'};
    const final=parser.parse(result.sql,metadata,{conditionQueries:true}),labels=new Set(final.scopes.map(q=>q.label));
    return {...result,field:model.fields[fieldId].alias,removed:[...new Set(removed)],retainedScopes:model.scopes.filter(q=>labels.has(q.label)).map(q=>q.id),retainedJoins:final.scopes.reduce((n,q)=>n+q.joins.length,0)};
    }catch(e){return {ok:false,reason:'简化后依赖校验未通过，保留原 SQL：'+e.message};}
  }
  function compareRows(original,simplified,index){
    if(!original||!simplified||!Array.isArray(original.rows)||!Array.isArray(simplified.rows))return {ok:false,reason:'宿主未返回可比对的行集。'};
    if(original.truncated!==false||simplified.truncated!==false)return {ok:false,reason:'宿主没有确认结果完整，不能判断一致。'};
    if(original.rows.length>=5000||simplified.rows.length>=5000)return {ok:false,reason:'结果达到读取上限，不能判断完整结果一致。'};
    if(!Array.isArray(original.columns)||!Number.isInteger(index)||index<0||simplified.columns?.length!==1||original.columns.length<=index)return {ok:false,reason:'输出列与所选字段不匹配。'};
    const encode=v=>{if(v===undefined)throw Error('结果含缺失值');if(typeof v==='number'&&(!Number.isFinite(v)||Number.isInteger(v)&&!Number.isSafeInteger(v)))throw Error('数值超过前端可靠精度范围，请由数据库比对');if(v===null)return 'null';if(typeof v==='object')return 'object:'+JSON.stringify(v);return typeof v+':'+String(v);};
    try{const counts=new Map();original.rows.forEach(r=>{const k=encode(r[index]);counts.set(k,(counts.get(k)||0)+1);});simplified.rows.forEach(r=>{const k=encode(r[0]);counts.set(k,(counts.get(k)||0)-1);});
      const equal=original.rows.length===simplified.rows.length&&[...counts.values()].every(n=>n===0);
      return {ok:true,equal,rows:original.rows.length,reason:equal?'本次完整读取结果一致（包含重复值和 NULL；不比较行顺序）。':'结果不一致，请保留原 SQL 并核对。'};
    }catch(e){return {ok:false,reason:'宿主结果无法逐值比较：'+e.message};}
  }
  return {generate,compareRows};
})();
if(typeof module!=='undefined'&&module.exports)module.exports=SQLSlice;
