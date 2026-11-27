const fs=require('fs'),path=require('path'),assert=require('assert/strict');
const {DatabaseSync}=require('node:sqlite'),L=require('./sql-logic.js'),S=require('./sql-slice.js');
const checks=[],db=new DatabaseSync(':memory:');
db.exec('CREATE TABLE a(id INTEGER, k INTEGER, v REAL); CREATE TABLE b(id INTEGER, k INTEGER, v REAL);');
for(let i=0;i<24;i++){db.prepare('INSERT INTO a VALUES (?,?,?)').run(i,i%5,i%7===0?null:(i-10)*3);if(i%3!==0)db.prepare('INSERT INTO b VALUES (?,?,?)').run(i,i%4,i*2);}
function compare(name,sql,mayRefuseBareOrder=false){const m=L.parse(sql);let generated=0,refused=0;m.root.fields.forEach((f,i)=>{const r=S.generate(m,f.id);if(!r.ok&&mayRefuseBareOrder){assert.match(r.reason,/需要保留内部多列及 ORDER BY/);refused++;return;}assert.ok(r.ok,name+': '+r.reason);generated++;const original=db.prepare(sql).all(),out=db.prepare(r.sql).all();
 const bag=xs=>xs.map(v=>JSON.stringify(v)).sort();assert.deepEqual(bag(out.map(r=>Object.values(r)[0])),bag(original.map(r=>Object.values(r)[i])),name+' / '+f.alias+'\n'+r.sql);});assert.ok(generated>0,name);if(mayRefuseBareOrder)assert.ok(refused>0,name+' explicitly guards cross-dialect bare ORDER BY wrapping');checks.push(name);}
compare('multi-layer projections and unused scalar/CTE removal',`WITH unused AS (SELECT SUM(v) AS z FROM b), vals AS (SELECT id,k,v,(SELECT SUM(v) FROM b) AS unrelated FROM a) SELECT id AS 编号,v*2 AS 金额,k FROM vals WHERE id>2 ORDER BY id`);
compare('LEFT JOIN duplicate rows retained; invalid cross-dialect ORDER wrapping refused',`SELECT a.v AS 金额,b.v AS 其他金额,a.id FROM a LEFT JOIN b ON a.k=b.k WHERE a.id<10 ORDER BY a.id`,true);
compare('ON 1=1 row multiplication retained',`SELECT a.v AS 金额,b.v AS 其他金额 FROM a LEFT JOIN b ON 1=1 WHERE a.id<2`);
compare('WHERE joined source filtering retained',`SELECT x.v AS 金额,y.v AS 其他金额 FROM (SELECT id,k,v FROM a) x JOIN (SELECT id,k,v FROM b WHERE v>4) y ON x.k=y.k WHERE y.id<16`);
compare('DISTINCT row grain retained with outer projection',`SELECT DISTINCT k AS 分类,v AS 金额 FROM a`);
compare('GROUP/HAVING aggregates retained including NULL',`SELECT k AS 分类,SUM(v) AS 金额,COUNT(*) AS 数量 FROM a GROUP BY k HAVING COUNT(*)>2`);
compare('aggregate keeps one row on empty input',`SELECT 1 AS 标记,SUM(v) AS 金额 FROM a WHERE id<0`);
compare('ORDER BY alias dependencies retained',`SELECT v*2 AS amount,id AS 编号 FROM a ORDER BY amount LIMIT 5`);
compare('ordinal ORDER/GROUP dependencies retained',`SELECT k AS 分类,SUM(v) AS 金额 FROM a GROUP BY 1 ORDER BY 2 DESC LIMIT 3`);
compare('UNION distinct multiplicities preserved',`SELECT k AS 分类,v AS 金额 FROM a UNION SELECT k,v FROM b`);
compare('shared CTE dependencies retained',`WITH x AS (SELECT id,k,v FROM a) SELECT l.v AS 左金额,r.v AS 右金额 FROM x l JOIN x r ON l.k=r.k WHERE r.id<3`);
compare('correlated scalar filter retains outer key',`SELECT id AS 编号,(SELECT SUM(b.v) FROM b WHERE b.k=a.k) AS 金额,v AS 原值 FROM a WHERE id<8`);
compare('window partition/order preserved',`SELECT id AS 编号,SUM(v) OVER(PARTITION BY k ORDER BY id) AS 累计,v AS 金额 FROM a ORDER BY id LIMIT 7`);
compare('explicit CTE column lists retain positional arity',`WITH x (编号,类别,金额) AS (SELECT id,k,v FROM a) SELECT 金额,编号 FROM x WHERE 类别=2`);
compare('quoted output aliases and zero-row results',`SELECT DISTINCT v AS "contract amount",id AS "order id" FROM a WHERE id<0`);
compare('comments cannot swallow the retained source clause',`SELECT id AS 编号, -- identifier\n v AS 金额, k AS 分类 FROM a WHERE id<5`);
compare('unlisted aggregate functions retain original row cardinality',`SELECT 1 AS flag,JSON_GROUP_ARRAY(v) AS values_json FROM a WHERE id<0`);
// LEN is a scalar function; it must not force unrelated output columns to be retained.
db.function('LEN', s=>s==null?null:String(s).length);
const lenSql='SELECT id AS selected, LEN(v) AS unrelated FROM a';
const lenModel=L.parse(lenSql),lenSlice=S.generate(lenModel,lenModel.root.fields[0].id);
assert.ok(lenSlice.ok);assert.ok(lenSlice.removed.some(x=>x.includes('unrelated')));
compare('LEN scalar allows unused projection pruning',lenSql);
// Column names that resemble volatile functions or pseudo-columns must not
// reject a slice when they are ordinary, unrelated output/source columns.
const uuidColumn=L.parse('SELECT x.v AS selected, x.UUID AS other FROM (SELECT v, UUID FROM a) x', undefined, {conditionQueries:true});
const uuidSlice=S.generate(uuidColumn, uuidColumn.root.fields[0].id);
assert.ok(uuidSlice.ok, 'ordinary UUID column must remain sliceable');
assert.equal(L.parse(uuidSlice.sql, undefined, {conditionQueries:true}).root.fields.length, 1);
assert.ok(!/\bUUID\s*\(/i.test(uuidSlice.sql));
checks.push('ordinary UUID column is not treated as UUID()');

const rownumColumn=L.parse('SELECT v AS selected, ROWNUM AS other FROM a', undefined, {conditionQueries:true});
const rownumSlice=S.generate(rownumColumn, rownumColumn.root.fields[0].id);
assert.ok(rownumSlice.ok, 'unrelated ROWNUM output must not block the selected field');
assert.equal(L.parse(rownumSlice.sql, undefined, {conditionQueries:true}).root.fields.length, 1);
assert.ok(!/\bROWNUM\b/i.test(rownumSlice.sql));
checks.push('unrelated ROWNUM output is not treated as a selected pseudo-column');

for (const [name, sql] of [
  ['selected UUID()', 'SELECT UUID() AS selected, v AS other FROM a'],
  ['selected ROWNUM', 'SELECT ROWNUM AS selected, v AS other FROM a']
]) {
  const model=L.parse(sql, undefined, {conditionQueries:true});
  const slice=S.generate(model, model.root.fields[0].id);
  assert.equal(slice.ok, false, name + ' must remain guarded');
  assert.match(slice.reason, /UUID|ROWNUM/);
}
checks.push('selected volatile function and pseudo-column remain guarded');

const unrelatedVolatileSubquery=L.parse('SELECT v AS selected, (SELECT UUID() FROM b) AS other FROM a', undefined, {conditionQueries:true});
assert.equal(S.generate(unrelatedVolatileSubquery, unrelatedVolatileSubquery.root.fields[0].id).ok, true);
checks.push('unrelated volatile scalar subquery does not block a safe slice');

const complexSql=fs.readFileSync(path.join(__dirname,'fixtures/complex-82-column-query.sql'),'utf8');
const complexModel=L.parse(complexSql, undefined, {conditionQueries:true});
assert.equal(complexModel.root.fields.length,82,'complex synthetic SQL output count');
let complexGenerated=0;
for (const field of complexModel.root.fields) {
  const slice=S.generate(complexModel,field.id);
  assert.ok(slice.ok,field.alias+': '+slice.reason);
  const slicedModel=L.parse(slice.sql,undefined,{conditionQueries:true});
  assert.equal(slicedModel.root.fields.length,1,field.alias+' must generate exactly one output');
  const repeated=S.generate(slicedModel,slicedModel.root.fields[0].id);
  assert.ok(repeated.ok,field.alias+': generated SQL must be re-sliceable');
  assert.equal(repeated.sql,slice.sql,field.alias+' must reach a stable SQL form');
  complexGenerated++;
}
const alertField=complexModel.root.fields[46];
assert.ok(alertField,'47th synthetic output is present');
const alertSlice=S.generate(complexModel,alertField.id);
assert.ok(alertSlice.ok,alertSlice.reason);
assert.equal(L.parse(alertSlice.sql,undefined,{conditionQueries:true}).root.fields.length,1);
checks.push('complex synthetic 82-field query: every output generates, reparses and reaches a stable one-field slice');
const natural=L.parse('SELECT a.v AS amount,b.v AS other FROM a NATURAL JOIN b');assert.equal(S.generate(natural,natural.root.fields[0].id).ok,false);checks.push('NATURAL JOIN refuses unsafe schema-dependent projection changes');
compare('unused singleton LEFT JOIN removed without changing duplicates',`SELECT a.v AS 金额,x.s AS 其他 FROM a LEFT JOIN (SELECT SUM(v) AS s FROM b) x ON a.id>5`);
compare('unused INNER JOIN false predicate retained',`SELECT a.v AS 金额,x.s AS 其他 FROM a JOIN (SELECT SUM(v) AS s FROM b) x ON a.id>5`);
compare('empty singleton aggregate driver replacement',`SELECT y.s AS 金额,x.s AS 其他 FROM (SELECT SUM(v) AS s FROM a WHERE id<0) x LEFT JOIN (SELECT SUM(v) AS s FROM b) y ON 1=1`);
compare('HAVING can remove singleton row so driver retained',`SELECT y.s AS 金额,x.s AS 其他 FROM (SELECT SUM(v) AS s FROM a HAVING COUNT(*)<0) x LEFT JOIN (SELECT SUM(v) AS s FROM b) y ON 1=1`);
compare('LIMIT zero invalidates exact singleton proof',`SELECT y.s AS 金额,x.s AS 其他 FROM (SELECT SUM(v) AS s FROM a LIMIT 0) x LEFT JOIN (SELECT SUM(v) AS s FROM b) y ON 1=1`);
compare('later ON requires earlier unused singleton',`SELECT a.v AS 金额,z.v AS 其他 FROM a LEFT JOIN (SELECT SUM(v) AS s FROM b) x ON 1=1 LEFT JOIN b z ON z.v=x.s`);
compare('nontrue singleton LEFT driver cannot be replaced',`SELECT y.s AS 金额,x.s AS 其他 FROM (SELECT SUM(v) AS s FROM a) x LEFT JOIN (SELECT SUM(v) AS s FROM b) y ON 1=0`);
const clipped=S.generate(L.parse('SELECT * FROM a'),'Q1:0');assert.equal(clipped.ok,false);checks.push('unsupported syntax never advertised as safe slice');
const result=(rows,truncated=false)=>({rows,columns:[{name:'v'}],truncated});
assert.equal(S.compareRows(result([[1],[1],[null]]),result([[null],[1],[1]]),0).equal,true);
assert.equal(S.compareRows(result([[1],[1],[null]]),result([[null],[1]]),0).equal,false);
assert.equal(S.compareRows(result([[1]],true),result([[1]]),0).ok,false);
assert.equal(S.compareRows({rows:[[1]],columns:[{}]},result([[1]]),0).ok,false);checks.push('comparison respects duplicates NULL types and incomplete result rejection');
assert.equal(S.compareRows({rows:[],truncated:false},result([]),0).ok,false);
assert.equal(S.compareRows(result([[1]]),result([['1']]),0).equal,false);
assert.equal(S.compareRows(result([[9007199254740992]]),result([[9007199254740992]]),0).ok,false);
assert.equal(S.compareRows(result(Array.from({length:5000},()=>[1])),result([[1]]),0).ok,false);
const collision=L.parse('SELECT DISTINCT a.id AS same,b.id AS same FROM a JOIN b ON a.k=b.k');
assert.equal(S.generate(collision,collision.root.fields[0].id).ok,false);checks.push('missing shape, type differences, capped reads and ambiguous aliases guarded');
db.close();const report={ok:true,checks};fs.writeFileSync(path.join(__dirname,'slice-verification.json'),JSON.stringify(report,null,2));console.log(JSON.stringify(report,null,2));
