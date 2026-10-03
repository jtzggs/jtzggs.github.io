/* 因子研究工作台：区间 / 收益窗口 / 预设方向 → 截面诊断 → 历史分段验证。 */
(function () {
'use strict';
var VERSION = 'factor-research-ui/1.1.0', STORAGE = 'mf_factor_research_options_v1';
var state = { options: null, result: null, comparison: null, correlation: null, snapshot: null,
  stale: false, running: false, selected: [], search: '', family: '', context: null, root: null, engine: null, renderedOnce: false };
var GROUPS = { all: '全体转债', 0: '偏债型', 1: '平衡型', 2: '偏股型' };
var pending = null, serial = 0, stagedDraft = null, continuation = null, candidateDirections = {}, archivedCandidatePlan = null;
function candidateDirection(k,g){return candidateDirections[k]===-1?-1:candidateDirections[k]===1?1:directionFor(k,g);}
function el(tag, cls, text) { var n = document.createElement(tag); if (cls) n.className = cls; if (text != null) n.textContent = text; return n; }
function empty(n) { while (n.firstChild) n.removeChild(n.firstChild); }
function copy(x) { return x == null ? x : JSON.parse(JSON.stringify(x)); }
function esc(x) { return String(x == null ? '' : x).replace(/[&<>"']/g, function (c) { return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]; }); }
function num(x, d) { return x == null || !Number.isFinite(Number(x)) ? '—' : Number(x).toFixed(d == null ? 3 : d); }
function pct(x, d) { return x == null || !Number.isFinite(Number(x)) ? '—' : (Number(x) * 100).toFixed(d == null ? 1 : d) + '%'; }
function sign(x) { return x == null || !Number.isFinite(Number(x)) ? '—' : (Number(x) > 0 ? '+' : '') + num(x, 3); }
function finite(x) { return x != null && Number.isFinite(Number(x)); }
function fields() { var c = state.context; return c ? (c.getFields ? c.getFields() : c.data.fields || []) : []; }
function field(k) { return fields().find(function (f) { return (f.k || f.key) === k; }); }
function name(k) { return k === '__score' ? '当前组合复合得分' : ((field(k) || {}).n || (field(k) || {}).name || k); }
function key(f) { return f.k || f.key; }
function family(f) { return f.family || f.c || '其他'; }
function available(f) { return f && f.selectable !== false && f.status !== 'unavailable'; }
function availableFields() { return fields().filter(available); }
function directionFor(k, g) {
  if (k === '__score') return 1;
  var c = state.context, f = field(k) || {}, v;
  if (c && c.getDirection) { try { v = c.getDirection(k, g === 'all' ? 1 : Number(g)); } catch (_) {} }
  if (v !== 1 && v !== -1) { v = Array.isArray(f.dir) ? f.dir[g === 'all' ? 1 : Number(g)] : f.dir; }
  return v === -1 ? -1 : 1;
}
function days() { var d = state.context.data, w = d.weeks || []; return d.period || [w.length ? w[0].d : '', w.length ? w[w.length - 1].d : '']; }
function yearsBefore(date, n) { if (!/^\d{4}-\d{2}-\d{2}$/.test(date || '')) return date; var a = new Date(date + 'T00:00:00Z'); a.setUTCFullYear(a.getUTCFullYear() - n); return a.toISOString().slice(0, 10); }
function suggestSplit(start,end) { var ds=(state.context.data.weeks||[]).map(function(w){return w.d;}).filter(function(d){return d>=start&&d<=end;});return ds.length>3?ds[Math.floor(ds.length*.67)]:''; }
function changeRange(partial) { var o=state.options,range=Object.assign({},o,partial);if(o.split&&(o.split<=range.start||o.split>=range.end))partial.split=suggestSplit(range.start,range.end);update(partial,true);var split=state.root.querySelector('#mfr-split');if(split)split.value=o.split||''; }
function initOptions() {
  if (state.options) return;
  var range = days(), start = yearsBefore(range[1], 3); if (start < range[0]) start = range[0];
  var saved; try { saved = JSON.parse(localStorage.getItem(STORAGE) || 'null'); } catch (_) {}
  state.options = Object.assign({ key: 'prem', group: 'all', direction: -1, start: start, end: range[1], horizon: 20,
    controls: [], rolling: 26, split: '', minPairs: 10, minPeriods: 20 }, saved || {}, pending || {});
  if (state.options.start < range[0] || state.options.start > range[1]) state.options.start = start;
  if (state.options.end > range[1] || state.options.end < range[0]) state.options.end = range[1];
  if ((!saved || !Object.prototype.hasOwnProperty.call(saved,'split')) && (!pending || !Object.prototype.hasOwnProperty.call(pending,'split'))) state.options.split=suggestSplit(state.options.start,state.options.end);
  normalize(); pending = null;
}
function normalize() {
  var o = state.options;
  o.group = o.group === 'all' ? 'all' : Number(o.group); if (o.group !== 'all' && [0,1,2].indexOf(o.group) < 0) o.group = 'all';
  if (!Array.isArray(o.controls)) o.controls = o.controls === 'price_parity_size' ? ['price','cb_value','issue_size_yi'] : [];
  o.direction = Number(o.direction) === -1 ? -1 : 1; o.horizon = Number(o.horizon); o.rolling = Number(o.rolling);
  if ([1,5,10,20,60].indexOf(o.horizon) < 0) o.horizon = 20;
  if ([26,52].indexOf(o.rolling) < 0) o.rolling = 26;
  if (o.key === '__score') o.direction = 1;
  if (o.key !== '__score' && !available(field(o.key))) { o.key = available(field('prem')) ? 'prem' : key(availableFields()[0] || {k:'prem'}); o.direction = directionFor(o.key, o.group); }
}
function persist() { try { localStorage.setItem(STORAGE, JSON.stringify(state.options)); } catch (_) {} }
function status(text, type) { var n = state.root && state.root.querySelector('[data-mfr-status]'); if (n) { n.textContent = text || ''; n.dataset.state = type || 'ready'; } }
function markChanged(notify) {
  normalize(); persist(); state.stale = !!state.result;
  if (state.root) {
    var result = state.root.querySelector('[data-mfr-results]'); if (result) result.dataset.stale = state.stale ? 'true' : 'false';
    state.root.querySelectorAll('[data-mfr-save]').forEach(function (b) { b.disabled = state.stale || !state.result; });
    var batch=state.root.querySelector('[data-mfr-batch]');if(batch){batch.remove();renderBatch();if(state.comparison)renderComparison();if(state.correlation)renderCorrelation();}
  }
  status(state.stale ? '参数已变更。下方仍是上次运行的结果（标题保留当时区间），请重新计算后再导出或保存。' : '参数已更新，点击“计算因子表现”查看当前条件下的结果。', state.stale ? 'stale' : 'ready');
  if (notify && state.context.onOptionsChange) state.context.onOptionsChange(copy(state.options));
}
function update(partial, notify) { Object.assign(state.options, partial); markChanged(notify); }
function button(text, action, cls) { var b = el('button', cls || '', text); b.type = 'button'; b.onclick = action; return b; }
function control(label, node) { var l = el('label', 'mfr-field'); l.appendChild(el('span', '', label)); l.appendChild(node); return l; }
function select(id, choices, value, change) { var s = el('select'); s.id = id; choices.forEach(function (v) { var op = el('option', '', v[1]); op.value = String(v[0]); s.appendChild(op); }); s.value = String(value); s.onchange = function () { change(s.value); }; return s; }
function dateInput(id, value, change) { var n = el('input'); n.id = id; n.type = 'date'; n.min = days()[0]; n.max = days()[1]; n.value = value || ''; n.onchange = function () { change(n.value); }; return n; }
function card(title, note) { var n = el('section', 'mfr-card'); if (title) n.appendChild(el('h4', '', title)); if (note) n.appendChild(el('p', 'mfr-subtle', note)); return n; }
function detail(title, content) { var n = el('details'); n.appendChild(el('summary', '', title)); var b = el('div'); if (typeof content === 'string') b.textContent = content; else b.appendChild(content); n.appendChild(b); return n; }
function list(lines) { var u = el('ul', 'mfr-method'); (lines || []).forEach(function (line) { u.appendChild(el('li', '', line)); }); return u; }
function renderFactorMeta(target) {
  empty(target); var o = state.options, f = field(o.key);
  if (o.key === '__score') { target.appendChild(el('strong', '', '检验当前组合的复合得分')); target.appendChild(el('p', 'mfr-subtle', '使用组合设置中已选择因子的方向与权重。全体转债时先计算各类型组内得分，再合并检验；同一次研究期间不自动调权。')); return; }
  if (!f) return;
  target.appendChild(el('strong', '', name(o.key))); target.appendChild(el('p', 'mfr-subtle', family(f) + ' · ' + o.key));
  target.appendChild(el('p', '', f.d || f.description || '暂无补充说明'));
  if(f.direction_hint===0)target.appendChild(el('p','mfr-subtle','暂无统一经济方向；当前方向仅为待验证假设，不代表该因子已被证实正向或负向有效。'));
  if (f.formula || f.expr) target.appendChild(el('code', '', '计算：' + (f.formula || f.expr)));
  var statusNames={available:'可研究',unavailable:'历史数据未覆盖',proxy:'使用代理口径',derived:'由历史字段计算',research:'研究口径'};
  var meta = []; if (f.unit) meta.push('单位：' + f.unit); if (f.lookback != null) meta.push('观察窗：' + f.lookback); if (f.status) meta.push('数据状态：' + (statusNames[f.status]||f.status));
  if (meta.length) target.appendChild(el('p', 'mfr-subtle', meta.join('；')));
  if(f.coverage){var cv=f.coverage;target.appendChild(el('p','mfr-subtle','整份历史数据覆盖：'+pct(cv.ratio,1)+'，'+(cv.valid_observations||0)+' 个有效观测；首末信号：'+(cv.first_signal||'—')+' 至 '+(cv.last_signal||'—')+'。本次研究覆盖率以重新计算的结果为准。'));}
  var notes = []; if (f.source) notes.push('来源：' + (Array.isArray(f.source)?f.source.join('、'):f.source)); if (f.limitations) notes = notes.concat(Array.isArray(f.limitations) ? f.limitations : [f.limitations]);
  if (notes.length) target.appendChild(detail('数据与口径限制', list(notes)));
}
function renderForm() {
  var root = state.root, o = state.options, c = card(); c.classList.add('mfr-config');
  var left = el('div'), right = el('div', 'mfr-config-main'); c.appendChild(left); c.appendChild(right);
  var search = el('input'); search.type = 'search'; search.id = 'mfr-factor-search'; search.placeholder = '搜索名称、公式或字段，如动量 / prem'; search.value = state.search;
  left.appendChild(control('研究因子', search));
  var families = Array.from(new Set(fields().map(family))).sort(), fam = select('mfr-factor-family', [['','全部因子类别']].concat(families.map(function (f) { return [f,f]; })), state.family, function (v) { state.family = v; fillFactors(); });
  fam.style.margin = '7px 0'; fam.setAttribute('aria-label','因子类别'); left.appendChild(fam);
  var fs = el('select', 'mfr-factor-select'); fs.id = 'mfr-factor'; fs.size = 7; fs.setAttribute('aria-label','选择研究因子'); left.appendChild(fs);
  var count = el('div', 'mfr-subtle'), fm = el('div','mfr-factor-meta'); left.appendChild(count); left.appendChild(fm);
  function fillFactors() {
    empty(fs); var q = state.search.trim().toLowerCase();
    var ff = fields().filter(function (f) { return (!state.family || family(f) === state.family) && (!q || [key(f),f.n,f.name,f.d,f.formula,family(f)].join(' ').toLowerCase().indexOf(q) >= 0); });
    if (!state.family && (!q || ('当前组合复合得分 __score').indexOf(q) >= 0)) { var composite = el('option','','当前组合复合得分'); composite.value = '__score'; fs.appendChild(composite); }
    ff.forEach(function (f) { var p = el('option', '', (f.n || f.name || key(f)) + ' · ' + family(f)+(available(f)?'':' · 数据未覆盖')); p.value = key(f);p.disabled=!available(f); fs.appendChild(p); });
    if (!Array.from(fs.options).some(function (p) { return p.value === o.key; })) { var keep = el('option', '', '当前：' + name(o.key)); keep.value = o.key; fs.insertBefore(keep, fs.firstChild); }
    fs.value = o.key; count.textContent = '当前匹配 ' + ff.length + ' 项；可研究 ' + availableFields().length + ' / 已定义 ' + fields().length + ' 项。相近窗口不等于独立信息。';
  }
  search.oninput = function () { state.search = search.value; fillFactors(); }; fillFactors();
  var dir = select('mfr-direction', [[1,'正向：值越高，预期收益越高'],[-1,'负向：值越低，预期收益越高']], o.direction, function (v) { update({direction:Number(v)}, true); });
  fs.onchange = function () { update({key:fs.value,direction:directionFor(fs.value,o.group)}, true); dir.value = String(o.direction); dir.disabled = o.key === '__score'; renderFactorMeta(fm); };
  var row = el('div','mfr-row'); row.appendChild(control('信号起始日期', dateInput('mfr-start',o.start,function (v) { changeRange({start:v}); }))); row.appendChild(control('研究结束日期',dateInput('mfr-end',o.end,function (v) { changeRange({end:v}); }))); right.appendChild(row);
  var shortcuts = el('div','mfr-shortcuts'); [[1,'近 1 年'],[3,'近 3 年'],[0,'全区间']].forEach(function (a) { shortcuts.appendChild(button(a[1],function () {
    var range = days(), start = a[0] ? yearsBefore(range[1],a[0]) : range[0]; if (start < range[0]) start = range[0];
    changeRange({start:start,end:range[1],split:suggestSplit(start,range[1])}); root.querySelector('#mfr-start').value = o.start; root.querySelector('#mfr-end').value = o.end;
  })); }); shortcuts.appendChild(el('small','','可用行情：' + days().join(' 至 '))); right.appendChild(shortcuts);
  row = el('div','mfr-row');
  row.appendChild(control('未来收益观察窗口',select('mfr-horizon',[1,5,10,20,60].map(function (h) { return [h,h + ' 个交易日']; }),o.horizon,function (v) { update({horizon:Number(v)},true); })));
  row.appendChild(control('研究样本池',select('mfr-group',[['all','全体转债'],[0,'偏债型'],[1,'平衡型'],[2,'偏股型']],o.group,function (v) { var g = v === 'all' ? 'all' : Number(v); update({group:g,direction:directionFor(o.key,g)},true); dir.value = String(o.direction); })));
  right.appendChild(row); row = el('div','mfr-row'); dir.disabled = o.key === '__score'; row.appendChild(control('事前设定的因子方向',dir));
  row.appendChild(control('滚动观察长度',select('mfr-rolling',[[26,'26 个周频截面（约半年）'],[52,'52 个周频截面（约一年）']],o.rolling,function (v) { update({rolling:Number(v)},true); }))); right.appendChild(row);
  row = el('div','mfr-row'); row.appendChild(control('历史训练 / 验证分界',dateInput('mfr-split',o.split,function (v) { update({split:v},true); })));
  row.appendChild(control('诊断时控制其他暴露',select('mfr-controls',[['none','原始因子（不做控制）'],['price_parity_size','控制价格、平价、发行规模']].concat(o.controls.length&&o.controls.length!==3?[['imported_controls','导入控制：'+o.controls.join(' / ')]]:[]),o.controls.length===3 ? 'price_parity_size' : o.controls.length ? 'imported_controls' : 'none',function (v) { update({controls:v === 'none' ? [] : v==='imported_controls'?o.controls:['price','cb_value','issue_size_yi']},true); }))); right.appendChild(row);
  right.appendChild(el('p','mfr-subtle','信号按周取样。收益标签从信号后第 1 个交易日收盘起算，窗口末日不得晚于研究结束日。改变区间或窗口后需重新计算。'));
  var advanced = el('div'); advanced.appendChild(el('p','mfr-subtle','价格、平价和发行规模控制仅用于本页诊断，并非行业中性化，也不会自动改变组合策略的打分。发行规模是余额代理；相关因子需留意口径依赖。'));
  advanced.appendChild(control('每期最少有效个券',select('mfr-minpairs',[10,20,30].concat([10,20,30].indexOf(o.minPairs)<0?[o.minPairs]:[]).map(function(n){return[n,n+' 只'];}),o.minPairs,function (v) { update({minPairs:Number(v)},true); })));
  advanced.appendChild(el('p','mfr-subtle','当前至少 '+o.minPeriods+' 个有效截面才提供统计推断；样本更短仅展示描述统计。'+(o.lag?'HAC 至少滞后 '+o.lag+' 期；':'')+'改变因子后再选方向，或反复尝试区间，都属于事后探索。'));
  right.appendChild(detail('进阶口径与样本门槛',advanced));
  var actions = el('div','mfr-actions mfr-actions-end');
  if (state.context.onUseFactor) actions.appendChild(button('加入策略构建',function () { if (o.key === '__score') { status('当前已经是组合复合得分，请在组合配置中调整组成因子。'); return; } state.context.onUseFactor(o.key,o.direction,o.group); status('已将因子和预设方向加入策略；组合回测将使用研究区间。诊断中的暴露控制不会自动加入组合。'); }));
  var run = button('计算因子表现',function () { runAnalysis(); },'mfr-primary'); run.dataset.mfrRun = 'true'; actions.appendChild(run); right.appendChild(actions); root.appendChild(c); renderFactorMeta(fm);
}
function metric(title, english, value, note) { var n = el('div','mfr-metric'); n.appendChild(el('div','mfr-metric-title',title)); n.appendChild(el('small','',english)); n.appendChild(el('div','mfr-metric-number',value)); n.appendChild(el('div','mfr-metric-note',note)); return n; }
function table(headers, rows) { var wrap = el('div','mfr-table-scroll'), t = el('table'), thead = el('thead'), tr = el('tr'); headers.forEach(function (h) { tr.appendChild(el('th',typeof h === 'object' && h.number ? 'mfr-num' : '',typeof h === 'object' ? h.text : h)); }); thead.appendChild(tr); t.appendChild(thead); var body = el('tbody'); rows.forEach(function (r) { var tr = el('tr'); r.forEach(function (v,i) { var td = el('td',typeof headers[i] === 'object' && headers[i].number ? 'mfr-num' : ''); if (v && typeof v === 'object' && v.nodeType) td.appendChild(v); else td.textContent = v == null ? '—' : String(v); tr.appendChild(td); }); body.appendChild(tr); }); t.appendChild(body); wrap.appendChild(t); return wrap; }
function H(text) { return {text:text,number:true}; }
function chartLine(series, dates, title) {
  var target = el('div','mfr-chart'), all = []; series.forEach(function (s) { (s.values || []).forEach(function (v) { if (finite(v)) all.push(Number(v)); }); });
  if (!all.length) { target.appendChild(el('div','mfr-empty','有效期数不足，暂不能绘制这条序列。')); return target; }
  var W=800, HT=232, L=55, R=15, T=17, B=36, low=Math.min(0,Math.min.apply(null,all)), high=Math.max(0,Math.max.apply(null,all)); if (high-low<.02) { low-=.01;high+=.01; } var pad=(high-low)*.08;low-=pad;high+=pad;
  function xx(i,n) { return L+(W-L-R)*(n<2?.5:i/(n-1)); } function yy(v) { return T+(HT-T-B)*(high-v)/(high-low); }
  var s='<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 '+W+' '+HT+'" role="img" aria-label="'+esc(title)+'"><title>'+esc(title)+'</title>';
  for(var g=0;g<5;g++){var v=low+(high-low)*g/4,y=yy(v);s+='<line x1="'+L+'" y1="'+y+'" x2="'+(W-R)+'" y2="'+y+'" stroke="#ede9f3"/><text x="'+(L-8)+'" y="'+(y+4)+'" text-anchor="end" fill="#797181" font-size="10">'+num(v,2)+'</text>';}
  s+='<line x1="'+L+'" y1="'+yy(0)+'" x2="'+(W-R)+'" y2="'+yy(0)+'" stroke="#bcb2cb" stroke-dasharray="4 4"/>';
  series.forEach(function (line) { var path='',active=false; line.values.forEach(function (v,i) { if(!finite(v)){active=false;return;} path+=(active?'L':'M')+xx(i,line.values.length).toFixed(2)+' '+yy(v).toFixed(2)+' ';active=true; });s+='<path d="'+path+'" stroke="'+line.color+'" stroke-width="'+(line.width||1.6)+'" fill="none"/>'; });
  [0,Math.floor((dates.length-1)/2),dates.length-1].forEach(function(i){if(i<0||!dates[i])return;s+='<text x="'+xx(i,dates.length)+'" y="'+(HT-11)+'" text-anchor="middle" fill="#797181" font-size="10">'+esc(dates[i])+'</text>';});
  s+='</svg>'; target.innerHTML=s; var legend=el('div','mfr-actions');series.forEach(function(l){var sp=el('span','mfr-subtle','━ '+l.name);sp.style.color=l.color;legend.appendChild(sp);});target.appendChild(legend);return target;
}
function quantileChart(qs) {
  var out=el('div','mfr-chart'), valid=qs.filter(function(q){return finite(q.meanReturn);});if(!valid.length){out.appendChild(el('div','mfr-empty','有效个券或五分位样本不足。'));return out;}
  var W=520,HT=235,L=57,R=15,T=18,B=42,vals=valid.map(function(q){return q.meanReturn;}),lo=Math.min(0,Math.min.apply(null,vals)),hi=Math.max(0,Math.max.apply(null,vals)); if(hi-lo<.0001){hi+=.0001;lo-=.0001;}var pad=(hi-lo)*.14;hi+=pad;lo-=pad;var y=function(v){return T+(HT-T-B)*(hi-v)/(hi-lo);},svg='<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 '+W+' '+HT+'" role="img" aria-label="五分位平均未来收益"><title>五分位平均未来收益，非净值曲线</title>';
  for(var j=0;j<5;j++){var z=lo+(hi-lo)*j/4;svg+='<line x1="'+L+'" y1="'+y(z)+'" x2="'+(W-R)+'" y2="'+y(z)+'" stroke="#ede9f3"/><text x="'+(L-8)+'" y="'+(y(z)+4)+'" text-anchor="end" font-size="10" fill="#797181">'+pct(z,2)+'</text>';}
  qs.forEach(function(q,i){var x=L+(W-L-R)*(i+.5)/5,top=y(Math.max(0,q.meanReturn||0)),height=Math.abs(y(q.meanReturn||0)-y(0));svg+='<rect x="'+(x-23)+'" y="'+top+'" width="46" height="'+Math.max(height,.5)+'" rx="3" fill="'+(i===4?'#6550a4':'#b8a8d5')+'"><title>Q'+q.q+'：'+pct(q.meanReturn,2)+'</title></rect><text x="'+x+'" y="'+(HT-22)+'" text-anchor="middle" font-size="11" fill="#5f566d">Q'+q.q+'</text>';});
  svg+='<line x1="'+L+'" y1="'+y(0)+'" x2="'+(W-R)+'" y2="'+y(0)+'" stroke="#bcb2cb"/></svg>';out.innerHTML=svg;return out;
}
function weightedPeriodMean(periods,k) { var a=periods.map(function(p){return p[k];}).filter(finite); return a.length?a.reduce(function(x,y){return x+Number(y);},0)/a.length:null; }
function renderResults() {
  var target=state.root.querySelector('[data-mfr-results]');empty(target);if(!state.result)return;
  var r=state.result,o=r.options||state.snapshot.spec,s=r.summary||{},cov=r.coverage||{},qs=r.quantiles||[],p=r.periods||[];
  target.dataset.stale=state.stale?'true':'false';
  var c=card(),heading=el('div','mfr-result-title'),title=el('div');title.appendChild(el('h3','',name(o.key)+' · 区间研究结果'));title.appendChild(el('div','mfr-result-meta',o.start+' 至 '+o.end+' · '+GROUPS[o.group]+' · 未来 '+o.horizon+' 个交易日 · '+(o.direction<0?'负向':'正向')+'预设 · '+(o.controls&&o.controls.length?'控制价格 / 平价 / 发行规模':'原始因子')));heading.appendChild(title);heading.appendChild(el('span','mfr-badge','周频截面 · '+(s.n||0)+' 期有效'));c.appendChild(heading);
  var metrics=el('div','mfr-metrics');metrics.appendChild(metric('排序预测能力','Rank IC 均值',num(s.meanIC,3),'比较预设方向后的因子排名与未来收益排名。'));
  metrics.appendChild(metric('预测稳定性','ICIR · 非年化',num(s.icir,2),'IC 均值 ÷ IC 标准差；不是策略夏普比率。'));
  metrics.appendChild(metric('方向正确期占比','Share of Rank IC > 0',pct(s.positiveShare,1),'有效截面中 IC > 0 的比例；不是持仓收益胜率。'));c.appendChild(metrics);
  var summary='';if(!s.n)summary='当前条件没有足够有效截面。先查看覆盖率、区间长度和数据缺失，再决定是否调整研究设定。';else if(s.descriptive)summary='样本较少，先按描述性结果阅读，不据此给出显著性结论。';else if(finite(s.meanIC))summary=s.meanIC>0?'在这段历史中，按当前预设方向排序与未来收益排名平均同向。能否用于策略，还需结合分段稳定性、覆盖率和交易成本。':s.meanIC<0?'在这段历史中，按当前预设方向排序与未来收益排名平均反向。页面保留这个结果，不会自动把因子翻转成“有效”。':'这段历史的平均排序关联接近零。请同时查看时期差异和样本覆盖。';
  c.appendChild(el('div','mfr-interpretation',summary));var coverage=el('div','mfr-coverage');['平均每期有效个券：'+num(cov.meanPairN,0),'因子覆盖率：'+pct(cov.factorCoverage,1),'收益标签覆盖率：'+pct(cov.labelCoverage,1),'研究截面：'+(cov.periods||0)+' 期'].forEach(function(v){coverage.appendChild(el('span','',v));});c.appendChild(coverage);
  var explain=el('div','mfr-explain');explain.textContent='怎样读：Rank IC = 0.05 表示较弱的正向排序关联，不代表赚 5%。负向因子（如“越低越好”）先乘以 −1，再计算本页主要指标。IC 可正可负，0 不计为方向正确。';c.appendChild(explain);
  var inference=[];inference.push('未乘方向的原始 Rank IC 均值：'+num(s.rawMeanIC,3)+'；本页方向调整后：'+num(s.meanIC,3)+'。');
  inference.push('均值的 95% 区间：'+(Array.isArray(s.ci95)?'['+num(s.ci95[0],3)+', '+num(s.ci95[1],3)+']':'样本不足或不可估计')+'；HAC t 值：'+num(s.hacT,2)+'；p 值：'+num(s.pValue,4)+'。');
  inference.push('未来收益窗口可能重叠，普通独立样本 t 检验不适用。这里按方法说明处理时序相关；同类因子重复尝试仍会增加偶然发现。');
  c.appendChild(detail('统计推断与原始方向（进阶）',list(inference)));
  var warnings=r.warnings||[];if(warnings.length)c.appendChild(detail('本次样本与数据限制 · '+warnings.length+' 项',list(warnings)));
  target.appendChild(c);
  var charts=card('排序能力是否随时间变化','细线展示每个周频截面的 Rank IC；粗线展示完整 '+o.rolling+' 期滚动均值。缺失期不补零，不跨缺口伪造完整窗口。');
  var rollMap={};(r.rolling||[]).forEach(function(v){rollMap[v.d]=v.meanIC;});charts.appendChild(chartLine([{name:'单期 Rank IC',color:'#c1b4d7',values:p.map(function(v){return v.ic;}),width:1.2},{name:o.rolling+' 期滚动均值',color:'#6550a4',values:p.map(function(v){return rollMap[v.d];}),width:2.5}],p.map(function(v){return v.d;}),'Rank IC 时序与滚动均值'));
  charts.appendChild(detail('查看逐期明细',table(['信号日期','标签终点',H('有效个券'),H('因子覆盖'),H('标签覆盖'),H('Rank IC'),H('Q5−Q1')],p.map(function(v){return [v.d,v.labelEnd||'—',v.pairN,pct(v.factorCoverage,1),pct(v.labelCoverage,1),num(v.ic,3),pct(v.spread,2)];}))));target.appendChild(charts);
  var two=el('div','mfr-two'),qcard=card('五分位检验','Q1 为预设方向后的低分组，Q5 为高分组。每期先按信号分组，再观察标签，不按未来是否有收益重选组。');qcard.appendChild(quantileChart(qs));
  qcard.appendChild(el('p','mfr-chart-note','平均 Q5−Q1：'+pct(weightedPeriodMean(p,'spread'),2)+'；Q5 相对同期样本池：'+pct(weightedPeriodMean(p,'topExcess'),2)+'。以上均是未来 '+o.horizon+' 日收益差，未扣交易成本。'));
  qcard.appendChild(el('p','mfr-subtle','这里显示各期未来收益的算术均值。重叠窗口不复利成净值，也不将高低差当作可交易多空策略。'));
  qcard.appendChild(detail('分组覆盖与收益明细',table(['分组',H('平均未来收益'),H('标签覆盖率'),H('有效期数')],qs.map(function(q){return ['Q'+q.q,pct(q.meanReturn,2),pct(q.coverage,1),q.periods==null?'—':q.periods];}))));two.appendChild(qcard);
  var split=card('历史分段验证','按所选分界分别观察训练段与验证段，跨越分界的收益标签应剔除。方向和参数若未经事前锁定，这只是历史分段，不是真正样本外。');
  var sp=r.split||{},rows=[];[['训练段',sp.train],['验证段',sp.validation]].forEach(function(a){var ss=a[1]&&a[1].summary||{},cc=a[1]&&a[1].coverage||{};rows.push([a[0],ss.n||0,num(ss.meanIC,3),num(ss.icir,2),pct(ss.positiveShare,1),pct(cc.factorCoverage,1)]);});
  split.appendChild(el('p','mfr-subtle','分界：'+(sp.date||o.split||'未设置')+'；剔除跨界标签：'+(sp.purgedPeriods||0)+' 期。'));
  split.appendChild(table(['区间',H('有效期数'),H('Rank IC'),H('ICIR'),H('方向正确期'),H('因子覆盖')],rows));split.appendChild(el('p','mfr-subtle','比较两段的方向、幅度与覆盖，不以验证段单次显著作为通过标准。需要真实样本外验证时，应先冻结配置再等待新数据。'));two.appendChild(split);target.appendChild(two);
  var annual=card('年度稳定性','观察不同年份是否保持相同方向；各年份期数和可用转债数可能差异明显。');
  annual.appendChild(table(['年份',H('有效期数'),H('Rank IC 均值'),H('ICIR'),H('方向正确期'),H('平均有效个券')],(r.annual||[]).map(function(v){return [v.period,v.n||0,num(v.meanIC,3),num(v.icir,2),pct(v.positiveShare,1),num((v.coverage||{}).meanPairN,0)];})));
  annual.appendChild(detail('月度表现明细',table(['月份',H('有效期数'),H('Rank IC 均值'),H('方向正确期')],(r.monthly||[]).map(function(v){return [v.period,v.n||0,num(v.meanIC,3),pct(v.positiveShare,1)];}))));target.appendChild(annual);
  var methods=card('方法、版本与保存');if(state.snapshot.continuation)methods.appendChild(el('p','mfr-subtle','本结果由研究档案复制条件后，使用当前版本新算。原档案：'+(state.snapshot.continuation.parent_id||state.snapshot.continuation.source_name||'外部档案')+'。条件变动与源版本信息已随结果保存，不宣称同版本复现。'));methods.appendChild(detail('完整研究方法',list(r.method||[])));var md=state.snapshot.metadata||{};methods.appendChild(el('p','mfr-subtle','数据版本：'+(md.data_version||'未提供')+'；研究引擎：'+(md.research_engine||'未提供')+'。保存结果冻结本次参数与完整诊断，不会把之后改动的参数写回旧档案。'));
  var actions=el('div','mfr-actions mfr-result-actions');var exp=button('导出研究 JSON',function(){download(snapshot(),'因子研究_'+o.key+'_'+o.start+'_'+o.end+'.json');});exp.dataset.mfrSave='true';exp.disabled=state.stale;actions.appendChild(exp);
  var save=button('保存到研究库',async function(){var snap=snapshot();if(!snap)return;save.disabled=true;try{if(typeof window.saveResearchRun==='function'){var receipt=await window.saveResearchRun(snap);status(receipt&&receipt.saved_to==='browser'?'因子研究已保存到浏览器研究库。':'研究结果已下载为 JSON，未存入浏览器研究库。');}else{download(snap,'因子研究_'+o.key+'.json');status('当前环境未提供研究库，已下载研究 JSON。');}}catch(e){status('保存失败：'+e.message,'error');}finally{save.disabled=state.stale;}},'mfr-primary');save.dataset.mfrSave='true';save.disabled=state.stale;actions.appendChild(save);methods.appendChild(actions);target.appendChild(methods);
  if(state.comparison)renderComparison();else{var cmp=state.root.querySelector('[data-mfr-comparison]');if(cmp)empty(cmp);}if(state.correlation)renderCorrelation();else{var cor=state.root.querySelector('[data-mfr-correlation]');if(cor)empty(cor);}
}
function researchKeys(){var o=state.result?state.result.options:state.options;return [o.key].concat(state.comparison?state.comparison.keys:[]).concat(state.correlation?state.correlation.keys:[]).filter(function(k){return !!k;});}
// A custom factor may reference another custom factor. Freeze the full custom
// definition set whenever one is used, so nested dependencies cannot drift.
function definitionKeys(keys){var all=fields(),custom=all.filter(function(f){return f.status==='custom'||f.c==='自定义';});if(keys.some(function(k){return custom.some(function(f){return key(f)===k;});}))keys=keys.concat(custom.map(key));return Array.from(new Set(keys));}
function composition(){return state.context.getComposition?copy(state.context.getComposition(state.options.group)):(state.context.getSelectedKeys?{keys:copy(state.context.getSelectedKeys(state.options.group)),replay_limitation:'未提供完整方向、权重与自定义公式'}:null);}
function contextSignature(){var keys=definitionKeys(researchKeys()),comp=keys.indexOf('__score')>=0?composition():null;if(comp){delete comp.created_at;delete comp.name;delete comp.research_diagnostics;}return JSON.stringify({data_version:(state.context.data.metadata||{}).data_version,code_version:(state.context.data.metadata||{}).code_version,definitions:keys.map(function(k){return field(k)||{k:k};}),composition:comp});}
function makeSnapshot() {
  var d=state.context.data,o=state.result.options||state.options,md=d.metadata||{},relevant=definitionKeys([o.key].concat(o.controls||[]).concat(state.comparison?state.comparison.keys:[]).concat(state.correlation?state.correlation.keys:[])),seen={};
  return {schema_version:'factor-research-run/1.0',kind:'factor-research',name:name(o.key)+' · '+o.start+' 至 '+o.end+' · '+o.horizon+'日',created_at:new Date().toISOString(),
    spec:copy(o),config:copy(o),metadata:{research_engine:window.MFResearch&&window.MFResearch.version,ui_version:VERSION,data_version:md.data_version,code_version:md.code_version,code_sha256:md.code_sha256,source_sha256:md.source_sha256,strict_pit:false,
      replay_status:'requires matching archived data and engine; not self-contained',limitations:copy(md.limitations||[])},factor_definitions:relevant.filter(function(k){if(!k||seen[k])return false;seen[k]=true;return true;}).map(function(k){return k==='__score'?{k:k,n:name(k),composition:composition()}:copy(field(k)||{k:k});}),
    continuation:copy(continuation),diagnostics:copy(state.result),comparison:copy(state.comparison),correlation:copy(state.correlation),result:copy(state.result)};
}
// Drafts are explicitly inspected before application. Never use normalize() to
// silently substitute a missing archived factor or an unsupported horizon.
function stable(value){if(Array.isArray(value))return '['+value.map(stable).join(',')+']';if(value&&typeof value==='object')return '{'+Object.keys(value).sort().map(function(k){return JSON.stringify(k)+':'+stable(value[k]);}).join(',')+'}';return JSON.stringify(value);}
function inspectDraft(value){
  var errors=[],warnings=[],v=value&&value.payload?value.payload:value;
  if(!v||v.kind!=='factor-research')return {errors:['只支持因子研究条件档案。'],warnings:[]};
  var o=copy(v.spec||v.config||{}),defs=copy(v.factor_definitions||[]),plan=copy(v.diagnostic_plan||{}),md=state.context&&state.context.data.metadata||{};
  if(!state.context)return {errors:['因子数据尚未加载。'],warnings:[]};
  if(!Array.isArray(defs))return {errors:['因子定义格式错误。'],warnings:[]};
  if(!/^[A-Za-z_][A-Za-z0-9_]*$/.test(o.key||''))errors.push('缺少有效的研究因子字段。');
  function date(d){return typeof d==='string'&&/^\d{4}-\d{2}-\d{2}$/.test(d)&&Number.isFinite(Date.parse(d+'T00:00:00Z'))&&new Date(d+'T00:00:00Z').toISOString().slice(0,10)===d;}
  if(!date(o.start)||!date(o.end)||o.start>o.end)errors.push('研究起止日期无效。');
  else if(o.start<days()[0]||o.end>days()[1])errors.push('档案区间超出当前行情覆盖（'+days().join(' 至 ')+'）；请先修改草稿区间，不会自动截短。');
  if(o.split&&(!date(o.split)||o.split<=o.start||o.split>=o.end))errors.push('历史分界必须位于起止日期之间。');
  if([1,5,10,20,60].indexOf(o.horizon)<0)errors.push('档案收益窗口不受支持。');
  if([1,-1].indexOf(o.direction)<0)errors.push('档案必须明确指定 +1 或 −1 方向。');
  if(o.key==='__score'&&o.direction!==1)errors.push('复合得分方向必须为 +1；各组成因子的方向由配置保存。');
  if(['all',0,1,2].indexOf(o.group)<0)errors.push('档案样本池不受支持。');
  if([26,52].indexOf(o.rolling)<0)errors.push('档案滚动窗口不受支持。');
  if(!Array.isArray(o.controls)||o.controls.some(function(k){return ['price','cb_value','issue_size_yi'].indexOf(k)<0;}))errors.push('档案控制变量不受支持。');
  ['minPairs','minPeriods'].forEach(function(k){if(!Number.isInteger(o[k])||o[k]<3)errors.push('档案 '+k+' 必须是至少 3 的整数。');});
  if(o.lag!=null&&(!Number.isInteger(o.lag)||o.lag<0))errors.push('档案 HAC 滞后参数无效。');
  var requested=[o.key].concat(Array.isArray(o.controls)?o.controls:[]);
  ['comparison','correlation'].forEach(function(k){var x=plan[k];if(!x)return;if(!Array.isArray(x.keys)||x.keys.length>(k==='comparison'?20:12)){errors.push('候选诊断列表超出支持范围。');return;}requested=requested.concat(x.keys);Object.keys(x.directions||{}).forEach(function(f){if([1,-1].indexOf(x.directions[f])<0)errors.push('候选因子方向无效：'+f);});});
  var score=defs.find(function(f){return f.k==='__score';}),comp=score&&score.composition;
  if(requested.indexOf('__score')>=0&&!comp)errors.push('复合得分档案缺少完整策略配置，不能用当前策略代替。');
  var adapter={errors:[],warnings:[]};
  if(state.context.inspectResearchDefinitions){try{adapter=state.context.inspectResearchDefinitions(defs,comp)||adapter;}catch(e){adapter.errors=[e.message];}}
  else {
    defs.filter(function(f){return f.status==='custom'||f.c==='自定义'||/^cf_/.test(f.k||'');}).forEach(function(f){var current=field(f.k);if(!current||(f.formula||f.expr)!==(current.formula||current.expr))errors.push('需要导入自定义因子及依赖：'+f.k);});
    if(comp)errors.push('当前工作台没有复合配置导入接口。');
  }
  errors=errors.concat(adapter.errors||[]);warnings=warnings.concat(adapter.warnings||[]);
  var incoming=defs.filter(function(f){return f.status==='custom'||f.c==='自定义'||/^cf_/.test(f.k||'');}).map(key);
  Array.from(new Set(requested)).forEach(function(k){if(k==='__score')return;if(incoming.indexOf(k)>=0&&state.context.applyResearchDefinitions)return;if(!available(field(k)))errors.push('当前数据缺少可计算字段：'+k);});
  defs.filter(function(f){return f.k!=='__score'&&incoming.indexOf(f.k)<0;}).forEach(function(f){var current=field(f.k);if(current&&f.formula&&f.formula!==current.formula)warnings.push('当前内置因子定义已变化：'+f.k+'；新运行使用当前定义。');});
  var versionChecks=[['数据版本','data_version'],['代码版本','code_version'],['代码指纹','code_sha256'],['数据源指纹','source_sha256']].map(function(pair){var old=(v.metadata||{})[pair[1]],now=md[pair[1]];return {label:pair[0],archived:old,current:now,status:old==null||now==null?'unknown':stable(old)===stable(now)?'match':'changed'};});
  var archivedEngine=(v.metadata||{}).research_engine;versionChecks.push({label:'研究引擎',archived:archivedEngine,current:window.MFResearch.version,status:!archivedEngine?'unknown':archivedEngine===window.MFResearch.version?'match':'changed'});
  versionChecks.forEach(function(c){if(c.status!=='match')warnings.push(c.label+(c.status==='changed'?'与档案不同。':'缺少可核验版本信息。'));});
  return {errors:Array.from(new Set(errors)),warnings:Array.from(new Set(warnings)),versionChecks:versionChecks,spec:o,definitions:defs,composition:comp,plan:plan,source:copy(v),parentId:value&&value.id||v.parent_id||null};
}
function stageDraft(value){if(state.running)throw Error('当前研究正在计算，请完成后再带入条件。');stagedDraft=copy(value);if(state.root){render(state.root,state.context);status('已载入待核验条件；查看版本与定义差异后，点击“使用当前版本继续研究”。原档案保持冻结。');}return state.context?inspectDraft(stagedDraft):null;}
function applyDraft(value){
  if(state.running)throw Error('请等待当前计算完成后再带入研究条件。');
  var check=inspectDraft(value||stagedDraft);if(check.errors.length)throw Error(check.errors.join('；'));
  var mapped={};if(state.context.applyResearchDefinitions)mapped=state.context.applyResearchDefinitions(check.definitions,check.composition)||{};
  var remap=mapped.keyMap||{},mapKey=function(k){return remap[k]||k;},o=copy(check.spec);o.key=mapKey(o.key);o.controls=o.controls.map(mapKey);
  state.options=o;candidateDirections={};var compare=check.plan.comparison||{},corr=check.plan.correlation||{};
  archivedCandidatePlan={comparison:(compare.keys||[]).map(mapKey),correlation:(corr.keys||[]).map(mapKey)};state.selected=Array.from(new Set((compare.keys||corr.keys||[o.key]).map(mapKey)));
  Object.keys(compare.directions||{}).forEach(function(k){candidateDirections[mapKey(k)]=compare.directions[k];});
  continuation={mode:'continue-with-current-version',parent_id:check.parentId,source_name:check.source.name||null,source_spec:check.spec,diagnostic_plan:copy(check.plan),source_metadata:copy(check.source.metadata||{}),version_checks:check.versionChecks,key_map:copy(remap),applied_at:new Date().toISOString(),note:'从冻结档案复制研究条件；新运行使用当前数据与引擎，不宣称同版本复现。'};
  stagedDraft=null;state.stale=!!state.result;state.comparison=null;state.correlation=null;persist();state.renderedOnce=true;
  if(state.root){render(state.root,state.context);markChanged(false);status('研究条件已带入。尚未计算；点击“计算因子表现”创建当前版本的新结果。原档案不变。');}
  return copy(continuation);
}
function renderDraft(){if(!stagedDraft)return;var check=inspectDraft(stagedDraft),c=card('从研究档案继续','先核验条件，再使用当前版本新建研究；不会覆盖或重新标注原报告。');c.dataset.mfrDraft='true';
  c.appendChild(el('p','',check.spec?name(check.spec.key)+' · '+check.spec.start+' 至 '+check.spec.end+' · '+check.spec.horizon+' 日 · '+(check.spec.direction<0?'负向':'正向'):'档案条件不可用'));
  if(check.versionChecks)c.appendChild(table(['核验项目','核验结果'],check.versionChecks.map(function(v){return[v.label,{match:'记录一致',changed:'版本不同',unknown:'无法核验'}[v.status]];})));
  c.appendChild(el('p','mfr-subtle','即使记录一致，也仅说明档案标识匹配；本次操作是继续研究，不是经过独立审计的逐项复现。'));
  if(check.errors.length)c.appendChild(list(check.errors));if(check.warnings.length)c.appendChild(detail('定义与版本差异',list(check.warnings)));
  var actions=el('div','mfr-actions'),apply=button('使用当前版本继续研究',function(){try{applyDraft();}catch(e){status('条件未带入：'+e.message,'error');}},'mfr-primary');apply.disabled=check.errors.length>0;actions.appendChild(apply);actions.appendChild(button('取消带入',function(){stagedDraft=null;render(state.root,state.context);}));c.appendChild(actions);state.root.appendChild(c);
}
function snapshot() { return state.snapshot && !state.stale ? copy(state.snapshot) : null; }
function download(value,filename){var blob=new Blob([JSON.stringify(value,null,2)],{type:'application/json;charset=utf-8'}),url=URL.createObjectURL(blob),a=el('a');a.href=url;a.download=filename;document.body.appendChild(a);a.click();a.remove();setTimeout(function(){URL.revokeObjectURL(url);},1000);}
function validate() { var o=state.options;if(!/^\d{4}-\d{2}-\d{2}$/.test(o.start)||!/^\d{4}-\d{2}-\d{2}$/.test(o.end)||o.start>o.end)throw Error('请设置有效的起止日期，起始日期不能晚于结束日期。');if(o.split&&(o.split<=o.start||o.split>=o.end))throw Error('历史分段日期需要位于起止日期之间；或清空分界，只做整段研究。'); }
function lock(busy) { state.running=busy; if(state.root)state.root.querySelectorAll('input,select,button').forEach(function(n){if(busy){n.dataset.mfrPreviousDisabled=n.disabled?'true':'false';n.disabled=true;}else{n.disabled=n.dataset.mfrPreviousDisabled==='true';delete n.dataset.mfrPreviousDisabled;}}); }
function yieldPaint(){return new Promise(function(resolve){setTimeout(resolve,20);});}
async function runAnalysis() {
  if(state.running)return;try{validate();}catch(e){status(e.message,'error');return;}var my=++serial;lock(true);status('正在按当前区间重新计算收益标签、每期相关性及五分位结果……','running');await yieldPaint();
  try{var result=state.engine.analyze(copy(state.options));if(my!==serial)return;state.result=result;state.stale=false;state.comparison=null;state.correlation=null;state.snapshot=makeSnapshot();state.signature=contextSignature();renderResults();var n=result.summary&&result.summary.n||0;status('计算完成：'+n+' 个有效周频截面。结果仅对应上方所示的已运行条件。');}catch(e){status('研究计算失败：'+e.message,'error');}finally{lock(false);}
}
function bh(rows){var valid=rows.map(function(r,i){return {i:i,p:r.pValue};}).filter(function(v){return finite(v.p)&&v.p>=0&&v.p<=1;}).sort(function(a,b){return a.p-b.p;});var last=1;for(var j=valid.length-1;j>=0;j--){last=Math.min(last,valid[j].p*valid.length/(j+1));rows[valid[j].i].bhQ=last;}return rows;}
function renderBatch() {
  var c=card('候选因子比较与重复信息检查','按同一区间、收益窗口和样本池比较；每个因子使用事先设定的方向。最多比较 20 个、相关性最多 12 个；先形成假设，再筛选候选。');
  c.dataset.mfrBatch='true';
  var opts=state.options,selectedKeys=state.context.getSelectedKeys?state.context.getSelectedKeys(opts.group):[];selectedKeys=(selectedKeys||[]).map(function(k){return typeof k==='string'?k:k.k;});
  if(!state.selected.length)state.selected=Array.from(new Set([opts.key].concat(selectedKeys))).filter(function(k){return k==='__score'||available(field(k));}).slice(0,12);
  var search=el('input');search.type='search';search.placeholder='筛选待比较因子';search.setAttribute('aria-label','筛选批量比较因子');c.appendChild(search);var picker=el('div','mfr-batch-picker');c.appendChild(picker);var count=el('span','mfr-subtle');
  function updateCount(){count.textContent='已选择 '+state.selected.length+' 个；比较≤20，相关性≤12。';}
  function draw(){empty(picker);var q=search.value.trim().toLowerCase();[{k:'__score',n:'当前组合复合得分',family:'复合'}].concat(availableFields()).filter(function(f){return !q||[key(f),f.n,family(f)].join(' ').toLowerCase().indexOf(q)>=0;}).forEach(function(f){var k=key(f),lab=el('label','mfr-check'),input=el('input');input.type='checkbox';input.checked=state.selected.indexOf(k)>=0;input.onchange=function(){if(input.checked){if(state.selected.length>=20){input.checked=false;status('批量诊断最多选择 20 个因子，请先缩小候选集合。','error');return;}state.selected.push(k);}else state.selected=state.selected.filter(function(v){return v!==k;});updateCount();};lab.appendChild(input);var t=el('span','',f.n||f.name||k);t.appendChild(el('small','',family(f)+' · '+((k===opts.key?opts.direction:candidateDirection(k,opts.group))>0?'+1':'−1')));lab.appendChild(t);picker.appendChild(lab);});updateCount();}
  search.oninput=draw;draw();var actions=el('div','mfr-actions');actions.appendChild(button('使用当前策略因子',function(){candidateDirections={};state.selected=Array.from(new Set(selectedKeys)).filter(function(k){return k==='__score'||available(field(k));}).slice(0,20);draw();}));if(archivedCandidatePlan){[['comparison','采用档案比较候选'],['correlation','采用档案相关性候选']].forEach(function(pair){if(archivedCandidatePlan[pair[0]].length)actions.appendChild(button(pair[1],function(){state.selected=archivedCandidatePlan[pair[0]].slice();if(pair[0]==='comparison'){var dirs=continuation.diagnostic_plan.comparison.directions||{},mapping=continuation.key_map||{};candidateDirections={};Object.keys(dirs).forEach(function(k){candidateDirections[mapping[k]||k]=dirs[k];});}draw();}));});}actions.appendChild(button('清空选择',function(){state.selected=[];draw();}));actions.appendChild(count);c.appendChild(actions);
  var progress=el('progress','mfr-progress');progress.max=1;progress.value=0;progress.style.display='none';progress.setAttribute('aria-label','因子比较进度');var msg=el('span','mfr-subtle');
  actions=el('div','mfr-actions mfr-actions-end');actions.appendChild(progress);actions.appendChild(msg);actions.appendChild(button('计算因子相关性',function(){runBatch(true,progress,msg);}));actions.appendChild(button('比较所选因子',function(){runBatch(false,progress,msg);},'mfr-primary'));c.appendChild(actions);
  c.appendChild(el('p','mfr-subtle','相关性衡量同一截面内因子排名是否重复，并非未来收益相关性。批量 p 值会按本次所选集合做 BH 校正；校正不能消除反复试区间、反复换候选的过拟合。'));
  var comparison=el('div');comparison.dataset.mfrComparison='true';c.appendChild(comparison);var corr=el('div');corr.dataset.mfrCorrelation='true';c.appendChild(corr);state.root.appendChild(c);
}
async function runBatch(isCorrelation,progress,msg) {
  if(state.running)return;var keys=state.selected.slice();if(!keys.length){status('请至少选择一个候选因子。','error');return;}if(isCorrelation&&(keys.length<2||keys.length>12)){status('相关性检查需要选择 2 至 12 个因子。','error');return;}if(keys.length>20){status('单次比较最多 20 个因子。','error');return;}try{validate();}catch(e){status(e.message,'error');return;}
  if(!state.result||state.stale){status('请先点击“计算因子表现”，确认本次研究条件，再运行候选比较。','stale');return;}
  var frozen=copy(state.result.options||state.options),dirs={};keys.forEach(function(k){dirs[k]=k===frozen.key?frozen.direction:candidateDirection(k,frozen.group);});frozen.directions=dirs;lock(true);progress.style.display='';progress.max=keys.length;progress.value=0;
  try{if(isCorrelation){msg.textContent='正在汇总 '+keys.length+' 个因子的截面相关性……';await yieldPaint();state.correlation=state.engine.correlations(keys,frozen);state.correlation.options=copy(frozen);progress.value=keys.length;renderCorrelation();}else{var rows=[],warnings=[];for(var i=0;i<keys.length;i++){msg.textContent='正在计算 '+(i+1)+' / '+keys.length+'：'+name(keys[i]);await yieldPaint();var one=state.engine.compare([keys[i]],frozen);(one.rows||[]).forEach(function(r){r.direction=dirs[r.key];rows.push(r);});warnings=warnings.concat(one.warnings||[]);progress.value=i+1;}
    state.comparison={keys:keys,options:frozen,rows:bh(rows),method:['每个因子均按显示的预设方向比较；不按绝对 IC 自动翻转。','p 值来自各因子 HAC 检验；BH q 值在本次有效 p 值集合内校正。','逐因子分别计算，缺失覆盖不同；比较时需同时检查样本数和覆盖率。'],warnings:Array.from(new Set(warnings))};renderComparison();}
    state.snapshot=makeSnapshot();state.signature=contextSignature();msg.textContent='已完成 '+keys.length+' 个因子';status('候选诊断已完成，导出或保存研究时会一并冻结这些结果。');
  }catch(e){status('候选诊断失败：'+e.message,'error');msg.textContent='计算失败';}finally{lock(false);}
}
function renderComparison(){var target=state.root.querySelector('[data-mfr-comparison]');if(!target||!state.comparison)return;empty(target);var c=state.comparison;target.appendChild(el('h4','','候选比较 · '+c.rows.length+' 个因子'));target.appendChild(el('p','mfr-subtle',(c.options||{}).start+' 至 '+(c.options||{}).end+' · 未来 '+(c.options||{}).horizon+' 日 · '+GROUPS[(c.options||{}).group]));target.appendChild(table(['因子','预设方向',H('有效期数'),H('Rank IC'),H('ICIR'),H('方向正确期'),H('标签覆盖'),H('HAC p'),H('BH q')],c.rows.map(function(v){var label=el('span','',v.name||name(v.key));label.appendChild(el('small','',v.key));return[label,v.direction<0?'负向 −1':'正向 +1',v.n||0,num(v.meanIC,3),num(v.icir,2),pct(v.positiveShare,1),pct((v.coverage||{}).labelCoverage,1),num(v.pValue,4),num(v.bhQ,4)];})));target.appendChild(detail('批量检验方法与限制',list((c.method||[]).concat(c.warnings||[]))));}
function renderCorrelation(){var target=state.root.querySelector('[data-mfr-correlation]');if(!target||!state.correlation)return;empty(target);var r=state.correlation;target.appendChild(el('h4','','因子相关性 · 截面秩相关的时间均值'));target.appendChild(el('p','mfr-subtle',(r.options||{}).start+' 至 '+(r.options||{}).end+' · '+GROUPS[(r.options||{}).group]+' · 原始方向'));var wrap=el('div','mfr-table-scroll'),t=el('table','mfr-correlation'),head=el('thead'),tr=el('tr');tr.appendChild(el('th','','因子'));r.keys.forEach(function(k,i){var th=el('th','','F'+(i+1));th.title=name(k);tr.appendChild(th);});head.appendChild(tr);t.appendChild(head);var body=el('tbody');r.keys.forEach(function(k,i){var tr=el('tr');tr.appendChild(el('th','','F'+(i+1)+' '+name(k)));r.keys.forEach(function(k2,j){var v=r.matrix[i][j],td=el('td','',num(v,2));if(finite(v)){td.style.background=v>=0?'rgba(101,80,164,'+(Math.abs(v)*.25)+')':'rgba(194,140,70,'+(Math.abs(v)*.25)+')';}td.title='有效配对截面：'+((r.counts[i]||[])[j]||0)+' 期';tr.appendChild(td);});body.appendChild(tr);});t.appendChild(body);wrap.appendChild(t);target.appendChild(wrap);target.appendChild(el('p','mfr-subtle','鼠标停留查看每对因子的有效截面期数。接近 +1 表示排序接近，接近 −1 表示排序相反；高相关不代表两个因子都有预测能力。'));target.appendChild(detail('相关性方法与限制',list((r.method||[]).concat(r.warnings||[]))));}
function render(root,context){state.context=context;state.root=root;initOptions();if(state.snapshot&&state.signature!==contextSignature())state.stale=true;state.engine=window.MFResearch.create(context.data,{valueGetter:context.valueGetter,scoreGetter:context.scoreGetter});empty(root);root.classList.add('mfr');var head=el('div','mfr-head'),title=el('div');title.appendChild(el('div','mfr-kicker','FACTOR RESEARCH'));title.appendChild(el('h3','','因子研究：先看区间，再判断有效性'));title.appendChild(el('p','mfr-muted','同一个因子在不同市场阶段、转债类型和收益窗口下，排序能力可能完全不同。这里把它作为待检验的研究假设。'));head.appendChild(title);head.appendChild(el('span','mfr-badge','可研究 '+availableFields().length+' / 已定义 '+fields().length));root.appendChild(head);renderDraft();renderForm();var stat=el('div','mfr-status');stat.dataset.mfrStatus='true';stat.setAttribute('role','status');stat.setAttribute('aria-live','polite');root.appendChild(stat);var results=el('div','mfr-results');results.dataset.mfrResults='true';root.appendChild(results);renderBatch();if(state.result){renderResults();if(state.stale)markChanged(false);}var first=!state.renderedOnce;state.renderedOnce=true;if(first&&!stagedDraft)setTimeout(function(){runAnalysis();},0);}
function setOptions(partial){if(!state.options){pending=Object.assign(pending||{},partial||{});return;}Object.assign(state.options,partial||{});normalize();persist();state.stale=!!state.result;if(state.root){render(state.root,state.context);markChanged(false);}}
window.MFResearchUI={version:VERSION,render:render,setOptions:setOptions,getOptions:function(){return copy(state.options||pending||{});},getSnapshot:snapshot,inspectDraft:inspectDraft,stageDraft:stageDraft,applyDraft:applyDraft};
window.getFactorResearchRunSnapshot=snapshot;
})();
