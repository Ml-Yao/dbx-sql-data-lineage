/* Offline SELECT dependency reader. Query scopes, not regex alias substitution.
 * Not a SQL validator or executor. Unsupported constructs remain explicit warnings.
 * CommonJS export is used by the regression suite; the same source is embedded in DBX. */
const SQLLogic = (() => {
  const KW = new Set(('SELECT DISTINCT ALL FROM WHERE GROUP BY HAVING ORDER ASC DESC NULLS FIRST LAST LIMIT OFFSET FETCH NEXT ROW ROWS ONLY TOP PERCENT WITH TIES UNION INTERSECT EXCEPT MINUS AS JOIN LEFT RIGHT FULL INNER OUTER CROSS NATURAL ON USING AND OR NOT IS NULL TRUE FALSE CASE WHEN THEN ELSE END IN EXISTS BETWEEN LIKE ILIKE ESCAPE REGEXP OVER PARTITION RANGE UNBOUNDED PRECEDING FOLLOWING CURRENT FILTER WITHIN KEEP DENSE_RANK IGNORE RESPECT NULLS DATE TIMESTAMP INTERVAL YEAR MONTH DAY HOUR MINUTE SECOND FOR AT TIME ZONE COLLATE VARCHAR VARCHAR2 CHAR NUMBER DECIMAL NUMERIC INTEGER INT BIGINT FLOAT DOUBLE PRECISION TEXT BOOLEAN SIGNED UNSIGNED QUALIFY CONNECT START PRIOR RECURSIVE MATERIALIZED').split(' '));
  const up = s => String(s || '').toUpperCase();
  function lex(sql) {
    const tokens=[], comments=[];
    let i=0;
    while(i<sql.length){
      const start=i, c=sql[i];
      if(/\s/.test(c)){ i++; continue; }
      if(sql.slice(i,i+2)==='--'){ i=sql.indexOf('\n',i); if(i<0)i=sql.length; comments.push({start,end:i,text:sql.slice(start+2,i).trim()});continue; }
      if(sql.slice(i,i+2)==='/*'){ const e=sql.indexOf('*/',i+2); if(e<0)throw Error('块注释未闭合');i=e+2; comments.push({start,end:i,text:sql.slice(start+2,e).trim()});continue; }
      let kind='symbol', value;
      if(c==="'" || c==='"' || c==='`' || c==='['){
        const end=c==='['?']':c; i++; let closed=false;
        while(i<sql.length){if(sql[i]===end){if(sql[i+1]===end){i+=2;continue;}i++;closed=true;break;}i++;}
        if(!closed)throw Error('字符串或标识符未闭合');
        kind=c==="'"?'string':'id';value=sql.slice(start+1,i-1).split(end+end).join(end);
      }else if(/[\p{L}_$#]/u.test(c)){
        i++;while(i<sql.length&&/[\p{L}\p{N}_$#]/u.test(sql[i]))i++;kind='word';value=sql.slice(start,i);
      }else if(/[0-9]/.test(c)){
        const m=sql.slice(i).match(/^\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/);i+=m[0].length;kind='number';value=m[0];
      }else{i++;value=c;}
      tokens.push({kind,value,raw:sql.slice(start,i),start,end:i,u:kind==='word'?up(value):value});
    }
    const stack=[];tokens.forEach((t,n)=>{if(t.kind==='symbol'&&t.value==='(')stack.push(n);if(t.kind==='symbol'&&t.value===')'){const p=stack.pop();if(p===undefined)throw Error('多余的右括号');t.pair=p;tokens[p].pair=n;}});
    if(stack.length)throw Error('括号未闭合');
    return {tokens,comments};
  }
  function parse(sql, metadata, options={}){
    const {tokens:t,comments}=lex(sql), scopes=[], physical=[], warnings=[], cache=new Map();
    if(t.slice(0,-1).some(x=>x.kind==='symbol'&&x.value===';'))throw Error('请一次解析一条 SELECT 查询');
    const word=(i,w)=>t[i]&&t[i].kind==='word'&&t[i].u===w;
    const sym=(i,w)=>t[i]?.kind==='symbol'&&t[i].value===w;
    const ident=i=>t[i]&&(t[i].kind==='word'||t[i].kind==='id');
    const raw=(a,b)=>a<b?sql.slice(t[a].start,t[b-1].end):'';
    const top=(a,b)=>{const r=[];for(let i=a;i<b;i++){r.push(i);if(sym(i,'('))i=t[i].pair;}return r;};
    const split=(a,b)=>{let p=a;const r=[];for(const i of top(a,b)){if(sym(i,',')){r.push([p,i]);p=i+1;}}if(p<b)r.push([p,b]);return r;};
    const note=(a,b)=>{if(a>=b)return '';const end=t[b-1].end;return comments.filter(c=>c.start>=end&&/^[, \t\r]*$/.test(sql.slice(end,c.start))).map(c=>c.text).join(' ');};
    function query(a,b,label,parent,environment,stack=[]){
      while(sym(b-1,';'))b--;
      while(sym(a,'(')&&t[a].pair===b-1){a++;b--;}
      if(scopes.length>240||stack.length>48)throw Error('查询层数过多，请缩小解析范围');
      const q={id:'Q'+(scopes.length+1),label,parent:parent?.id||null,fields:[],sources:[],joins:[],clauses:{},clauseRanges:{},definitions:[],warnings:[],env:{...environment},range:[a,b]};scopes.push(q);
      if(word(a,'WITH')){
        const withStart=a;
        a++;if(word(a,'RECURSIVE')){q.warnings.push('递归 CTE：递归分支不展开');a++;}
        while(ident(a)){
          const declarationStart=a,name=t[a++].value;let names=[];
          if(sym(a,'(')){names=split(a+1,t[a].pair).map(([s])=>t[s].value);a=t[a].pair+1;}
          if(!word(a,'AS'))throw Error('CTE 缺少 AS：'+name);a++;
          if(word(a,'NOT'))a++;if(word(a,'MATERIALIZED'))a++;
          if(t[a]?.value!=='(')throw Error('CTE 缺少查询体：'+name);
          const def={a:a+1,b:t[a].pair,name,names};q.env[up(name)]=def;a=t[a].pair+1;
          q.definitions.push({...def,range:[declarationStart,a]});
          if(t[a]?.value!==',')break;a++;
        }
        q.withRange=[withStart,a];
      }
      const unions=top(a,b).filter(i=>['UNION','INTERSECT','EXCEPT','MINUS'].some(w=>word(i,w)));
      if(unions.length){
        let p=a; q.branches=[];q.setOps=[];
        for(const end of [...unions,b]){
          q.branches.push(query(p,end,label+' / 分支 '+(q.branches.length+1),q,q.env,stack));
          if(end<b){q.setOps.push(t[end].u+(word(end+1,'ALL')?' ALL':''));p=end+1+(word(end+1,'ALL')||word(end+1,'DISTINCT')?1:0);}
        }
        q.fields=q.branches[0].fields.map((f,i)=>({...f,id:q.id+':'+i,scope:q.id,unionIndex:i,deps:null}));
        if(q.branches.some(x=>x.fields.length!==q.fields.length))q.warnings.push('集合查询各分支列数不同');
        return q;
      }
      if(!word(a,'SELECT'))throw Error('目前仅展开 SELECT / WITH 查询');
      const positions=top(a+1,b).filter(i=>['FROM','WHERE','GROUP','HAVING','ORDER','LIMIT','OFFSET','FETCH','QUALIFY','CONNECT','START'].some(w=>word(i,w)));
      const first=positions[0]??b;let selectStart=a+1;
      if(word(selectStart,'DISTINCT')||word(selectStart,'UNIQUE')||word(selectStart,'ALL')){q.distinct=word(selectStart,'UNIQUE')?'DISTINCT':t[selectStart].u;selectStart++;}
      if(q.distinct==='DISTINCT'&&word(selectStart,'ON'))q.warnings.push('DISTINCT ON 暂未展开，请保留原 SQL');
      if(word(selectStart,'TOP')){const st=selectStart++;if(t[selectStart]?.value==='(')selectStart=t[selectStart].pair+1;else selectStart++;if(word(selectStart,'PERCENT'))selectStart++;if(word(selectStart,'WITH')&&word(selectStart+1,'TIES'))selectStart+=2;q.clauses.TOP=raw(st,selectStart);}
      // Dialect extensions are explicit boundaries, never ordinary field names.
      const unsupported=new Set('WINDOW PIVOT UNPIVOT MATCH_RECOGNIZE MODEL APPLY LATERAL TABLESAMPLE SAMPLE SQL_CALC_FOUND_ROWS DISTINCTROW PREWHERE SETTINGS FORMAT SEMI ANTI ASOF STRAIGHT_JOIN ARRAY'.split(' '));
      for(const i of top(a,b))if(t[i].kind==='word'&&unsupported.has(t[i].u)&&!word(i-1,'AS')&&!sym(i-1,'.')&&!sym(i+1,'.')&&(i>=first||['SQL_CALC_FOUND_ROWS','DISTINCTROW'].includes(t[i].u)))q.warnings.push(t[i].u+' 方言语法暂未展开，请保留原 SQL');
      q.projection=[selectStart,first];
      for(let n=0;n<positions.length;n++){
        const p=positions[n], end=positions[n+1]??b, kw=t[p].u;
        if(kw!=='FROM'){const start=p+1+((kw==='GROUP'||kw==='ORDER')&&word(p+1,'BY')?1:0);q.clauses[kw]=raw(start,end);q.clauseRanges[kw]=[start,end];}
        if(['CONNECT','START'].includes(kw))q.warnings.push('层次查询条件保留原文，未展开递归依赖');
        if(kw==='FROM'){q.fromRange=[p+1,end];sources(p+1,end,q,stack);}
      }
      q.fields=split(selectStart,first).map(([s,e],n)=>{
        let exprEnd=e,alias='', inds=top(s,e), as=inds.filter(i=>word(i,'AS')).pop();
        if(as!==undefined&&as===e-2&&ident(e-1)){alias=t[e-1].value;exprEnd=as;}
        else if(e-s>1&&ident(e-1)&&!KW.has(t[e-1].u)&&t[e-2].value!=='.'&&(t[e-2].value===')'||t[e-2].kind==='number'||t[e-2].kind==='string'||ident(e-2))){alias=t[e-1].value;exprEnd=e-1;}
        if(!alias){alias=ident(e-1)?t[e-1].value:raw(s,e);}
        const f={id:q.id+':'+n,scope:q.id,alias,aliasSQL:ident(e-1)?t[e-1].raw:null,expr:raw(s,exprEnd),range:[s,exprEnd],outputRange:[s,e],comment:note(s,e),scalar:[]};
        for(let i=s;i<exprEnd;i++)if(sym(i,'(')&&(word(i+1,'SELECT')||word(i+1,'WITH'))){const end=t[i].pair;const sub=query(i+1,end,label+' / '+alias+' · 标量子查询',q,q.env,stack);f.scalar.push({start:i,end,query:sub.id});i=end;}
        return f;
      });
      // Preserve unsupported row subqueries explicitly; do not claim their lineage is complete.
      if(options.conditionQueries){
        q.conditionQueries=[];
        for(const [clause,range] of [...Object.entries(q.clauseRanges).filter(([k])=>['WHERE','HAVING','QUALIFY'].includes(k)),...q.joins.filter(j=>j.range).map(j=>['ON',j.range])]){
          for(let i=range[0];i<range[1];i++)if(sym(i,'(')&&(word(i+1,'SELECT')||word(i+1,'WITH'))){const end=t[i].pair,sub=query(i+1,end,label+' / '+clause+' 条件子查询',q,q.env,stack);q.conditionQueries.push({start:i,end,query:sub.id});i=end;}
        }
      }else for(const k of ['WHERE','HAVING','QUALIFY'])if(/\b(?:SELECT|WITH)\b/i.test(q.clauses[k]||''))q.warnings.push(k+' 含子查询：条件保留原文，条件子查询依赖未展开');
      return q;
    }
    function sources(a,b,q,stack){
      let i=a,previous=null,type='FROM';
      while(i<b){
        const joinStart=i;
        if(sym(i,',')){type='CROSS JOIN';i++;}
        const jt=[];while(i<b&&['LEFT','RIGHT','FULL','INNER','OUTER','CROSS','NATURAL','JOIN'].some(w=>word(i,w)))jt.push(t[i++].u);
        if(jt.length)type=jt.join(' ');
        const st=i;let name='',child=null,names=[],isSub=false;
        if(sym(i,'(')){const end=t[i].pair;child=query(i+1,end,q.label+' / 子查询',q,q.env,stack);i=end+1;isSub=true;}
        else if(ident(i)){
          names.push(t[i++].value);while(t[i]?.value==='.'&&ident(i+1)){i++;names.push(t[i++].value);}name=names.join('.');
          if(sym(i,'(')){q.warnings.push('表值函数 '+name+' 的内部依赖未展开');i=t[i].pair+1;}
        }else{q.warnings.push('未展开 FROM 片段：'+raw(i,b));break;}
        if(word(i,'AS'))i++;
        let alias=name.split('.').pop()||'子查询';
        if(ident(i)&&(!KW.has(t[i].u)||t[i].kind==='id'))alias=t[i++].value;
        const def=q.env[up(name)];
        if(def){
          if(stack.includes(def)){q.warnings.push('递归引用 '+name+'：未展开循环');}
          else{const key=def.a+':'+def.b;if(!cache.has(key)){cache.set(key,query(def.a,def.b,def.name,null,q.env,[...stack,def]));}child=cache.get(key);if(def.names.length)child.fields.forEach((f,n)=>{f.alias=def.names[n]||f.alias;});}
        }
        const src={id:child?child.id:q.id+'_T'+q.sources.length,alias,name:name||alias,query:child?.id||null,scope:q.id,comment:note(st,i),range:[st,i]};
        if(!child){src.schema=names.slice(0,-1).join('.');src.table=names.at(-1)||alias;physical.push(src);}
        if(isSub)child.label=alias+' · 子查询';
        q.sources.push(src);
        if(previous){
          let condition='',kind='';
          if(word(i,'ON')||word(i,'USING')){
            kind=t[i++].u;const start=i;
            while(i<b){if(sym(i,'(')){i=t[i].pair+1;continue;}if(sym(i,',')||['LEFT','RIGHT','FULL','INNER','CROSS','NATURAL','JOIN'].some(w=>word(i,w)))break;i++;}
            condition=raw(start,i);
          }
          const conditionRange=kind?[i-lex(condition).tokens.length,i]:null;
          q.joins.push({left:previous.id,right:src.id,leftAlias:previous.alias,rightAlias:alias,type,kind,condition,range:conditionRange,fullRange:[joinStart,i]});
        }
        previous=src;type='JOIN';
        if(i===st)break;
      }
    }
    const root=query(0,t.length,'最终结果',null,{}), byId=Object.fromEntries(scopes.map(q=>[q.id,q]));
    const sourceById=Object.fromEntries(physical.map(s=>[s.id,s]));
    // A missing dictionary entry is different from a known table without this
    // column. Cache per source; never search unrelated tables in the dictionary.
    const columnMetadata=new Map();
    function sourceColumns(s){
      if(!columnMetadata.has(s.id))columnMetadata.set(s.id,metadata?.(s));
      return columnMetadata.get(s.id);
    }
    function resolve(q,name,qualifier){
      let candidates=q.sources.filter(s=>!qualifier||up(s.alias)===up(qualifier)||up(s.name)===up(qualifier));
      let resolution='';
      if(!qualifier&&candidates.length>1){
        const undecidable=new Set();
        candidates=candidates.filter(s=>{
          if(s.query){const fields=byId[s.query].fields;if(fields.some(f=>up(f.alias)===up(name)))return true;
            if(fields.some(f=>f.expr==='*'||/\.\s*\*$/.test(f.expr))){undecidable.add(s.id);return true;}return false;}
          const columns=sourceColumns(s);if(!Array.isArray(columns)){undecidable.add(s.id);return true;}
          return columns.some(c=>up(c)===up(name));
        });
        if(candidates.length===1)resolution=undecidable.has(candidates[0].id)?'dictionary-exclusion':'dictionary';
      }
      if(candidates.length===1){const s=candidates[0];if(s.query){const matches=byId[s.query].fields.filter(f=>up(f.alias)===up(name));if(matches.length===1)return {kind:'field',id:matches[0].id};return {kind:'unknown',name:(qualifier?qualifier+'.':'')+name,reason:'来源查询未找到唯一输出列'};}return {kind:'column',source:s.id,column:name,...(resolution?{resolution}:{})};}
      if(!candidates.length&&q.parent)return resolve(byId[q.parent],name,qualifier);
      return {kind:'unknown',name:(qualifier?qualifier+'.':'')+name,reason:candidates.length?'字典核对后仍有多个候选来源：'+candidates.map(s=>s.name+' AS '+s.alias).join('、'):'未找到来源'};
    }
    function dependencies(q,f){
      if(f.unionIndex!==undefined)return q.branches.map(b=>b.fields[f.unionIndex]?{kind:'field',id:b.fields[f.unionIndex].id}:{kind:'unknown',name:f.alias,reason:'集合分支缺列'});
      const refs=[],[a,b]=f.range;
      for(let i=a;i<b;i++){
        const scalar=f.scalar.find(s=>s.start===i);
        if(scalar){const sq=byId[scalar.query];refs.push(sq.fields.length===1?{kind:'field',id:sq.fields[0].id}:{kind:'unknown',name:f.alias,reason:'标量子查询输出不是一列'});i=scalar.end;continue;}
        if(t[i].kind==='symbol'&&t[i].value==='*'&&(i===a||['(','.'].includes(t[i-1]?.value))){
          if(i>a&&word(i-1,'('))continue;
          q.sources.forEach(s=>refs.push({kind:'rows',source:s.id}));if(i===a||i===b-1&&t.slice(a,i).every(x=>['word','id'].includes(x.kind)||x.kind==='symbol'&&x.value==='.'))q.warnings.push('SELECT * / 表别名.* 未自动展开，请用明确列名核对字段链路');continue;
        }
        if(!ident(i)||t[i].kind==='word'&&KW.has(t[i].u)||t[i-1]?.value===':'||t[i+1]?.value==='(')continue;
        const parts=[t[i].value];while(t[i+1]?.value==='.'&&ident(i+2)){parts.push(t[i+2].value);i+=2;}
        if(t[i+1]?.value==='(')continue;
        refs.push(resolve(q,parts.at(-1),parts.length>1?parts.slice(0,-1).join('.'):null));
      }
      return [...new Map(refs.map(r=>[JSON.stringify(r),r])).values()];
    }
    scopes.forEach(q=>q.fields.forEach(f=>{
      f.deps=dependencies(q,f);f.aggregate=false;f.groupAggregate=false;f.window=false;
      // Inspect function tokens, never literal/comment text. A projection may
      // combine an ordinary aggregate, a window and a scalar subquery.
      for(let i=f.range[0];i<f.range[1];i++){
        const sub=f.scalar.find(s=>s.start===i);if(sub){i=sub.end;continue;}
        if(t[i].kind!=='word'||t[i+1]?.value!=='(')continue;
        if(t[i].u==='OVER'){f.window=true;continue;}
        if(!/^(SUM|AVG|COUNT|MIN|MAX|LISTAGG|STRING_AGG|ARRAY_AGG|STDDEV|VARIANCE)$/.test(t[i].u))continue;
        // SQLite MIN/MAX with multiple arguments are scalar; conservative in
        // every dialect, since names alone cannot prove aggregate cardinality.
        if(/^(MIN|MAX)$/.test(t[i].u)&&split(i+2,t[i+1].pair).length!==1)continue;
        f.aggregate=true;
        let end=t[i+1].pair+1;
        for(const suffix of ['WITHIN','FILTER','KEEP']){
          if(word(end,suffix)){
            end++;if(word(end,'GROUP'))end++;
            if(t[end]?.value==='(')end=t[end].pair+1;
          }
        }
        if(!word(end,'OVER'))f.groupAggregate=true;
      }
      f.conditional=/\bCASE\b|\bFILTER\s*\(|\b(?:IF|IFF)\s*\(/i.test(f.expr)&&!f.scalar.length;
      if(f.aggregate&&!f.deps.length)f.deps=q.sources.map(s=>({kind:'rows',source:s.id}));
    }));
    const fields=Object.fromEntries(scopes.flatMap(q=>q.fields.map(f=>[f.id,f])));
    function trace(id){
      const visited=new Set(),steps=[],leaves=[],unknown=[],links=[];
      function visit(key,depth){if(visited.has(key))return;visited.add(key);const f=fields[key];if(!f)return;const q=byId[f.scope];
        for(const d of f.deps){if(d.kind==='field'){links.push({from:fields[d.id]?.scope,to:q.id,column:fields[d.id]?.alias,output:f.alias});visit(d.id,depth+1);}else if(d.kind==='column'||d.kind==='rows'){leaves.push(d);links.push({from:d.source,to:q.id,column:d.column||'*',output:f.alias});}else unknown.push(d);}
        steps.push({field:f,scope:q,depth});
      }
      visit(id,0);return {steps,leaves:[...new Map(leaves.map(d=>[JSON.stringify(d),d])).values()],unknown,links,warnings:[...new Set(steps.flatMap(s=>s.scope.warnings))]};
    }
    scopes.forEach(q=>warnings.push(...q.warnings));
    function references(scope,range){
      const q=byId[scope],parts=[];let start=range[0];
      for(const sub of q.conditionQueries||[]){if(sub.start<start||sub.end>=range[1])continue;if(start<sub.start)parts.push([start,sub.start]);start=sub.end+1;}
      if(start<range[1])parts.push([start,range[1]]);
      return parts.flatMap(part=>dependencies(q,{range:part,scalar:[]})).flatMap(d=>{
        const f=q.fields.find(f=>up(f.alias)===up(d.name||d.column));
        return f?[d,{kind:'field',id:f.id}]:[d];
      });
    }
    return {root,scopes,physical,byId,sourceById,fields,trace,references,tokens:t,warnings:[...new Set(warnings)],sql};
  }
  return {parse,lex};
})();
if(typeof module!=='undefined'&&module.exports)module.exports=SQLLogic;
