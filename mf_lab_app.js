/* ============================================================================
 * 多因子分析 · 浏览器端应用逻辑
 * 数据：multifactor_lab_data.p1..pN.js 分片（MF_LAB_DATA_PARTS → window.MF_LAB_DATA，懒加载；兼容旧单文件）
 * 口径：与 cb_multifactor_backtest.py（研报分类型多因子框架本地实现）一致
 *   - 三分类（平底溢价率：<-20% 偏债 / ±20% 平衡 / >20% 偏股）
 *   - 组内 MAD去极值(±3×1.4826×MAD) → 截面ZSCORE → 缺失填0
 *   - 复合得分 = mean(dir × z)，前 topRatio 等权多头
 *   - 信号日收盘 → T+1收盘成交，双边成本；浏览器版按日行情维护数量与现金，周度展示，
 *     Python研究复核见 run_lab_config.py（同一数量/现金/换手契约；非完整总收益）
 * ============================================================================ */
(function () {
'use strict';

/* ------------------------------ 全局状态 ------------------------------ */
var D = null;                 // window.MF_LAB_DATA
var FIELDS = null, FIDX = {}, BONDS = null, WEEKS = null, GROUPS = null;
var CONSTS = null, REF = null, IDXNAV = null, ICMETA = null, DEFAULTS = null;
var CFG = null;               // 用户配置
var LAST_BT = null;           // 最近一次回测结果
var VIEW = 'ic';          // 当前子视图
var CUR_GROUP = 0;            // 因子库当前组
var IC_GROUP = 0;             // IC验证当前组
var dataLoaded = false, dataLoading = false, booted = false, dataWaiters=[];
var exprCache = {};

var LS_KEY = 'mf_lab_cfg_v2';
var CUSTOM_KEYS = 'cf_';

/* ------------------------------ DOM 工具 ------------------------------ */
function $(id) { return document.getElementById(id); }
function h(tag, cls, text) {
  var e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text != null) e.textContent = text;
  return e;
}
function clear(node) { while (node.firstChild) node.removeChild(node.firstChild); }
function fmtPct(x, d) {
  if (x == null || !isFinite(x)) return '—';
  return (x >= 0 ? '' : '') + (x * 100).toFixed(d == null ? 2 : d) + '%';
}
function fmtPctS(x, d) {
  if (x == null || !isFinite(x)) return '—';
  return (x >= 0 ? '+' : '') + (x * 100).toFixed(d == null ? 2 : d) + '%';
}
function fmtN(x, d) {
  if (x == null || !isFinite(x)) return '—';
  return Number(x).toFixed(d == null ? 2 : d);
}
function esc(s) {
  return String(s).replace(/[&<>"']/g, function (c) {
    return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
  });
}

/* ------------------------------ 数学工具 ------------------------------ */
function mean(a) {
  var s = 0, n = 0;
  for (var i = 0; i < a.length; i++) if (a[i] != null && isFinite(a[i])) { s += a[i]; n++; }
  return n ? s / n : NaN;
}
function stdev(a) {  // 样本标准差（ddof=1，与 pandas 一致）
  var m = mean(a), s = 0, n = 0;
  for (var i = 0; i < a.length; i++) if (a[i] != null && isFinite(a[i])) { s += (a[i] - m) * (a[i] - m); n++; }
  return n > 1 ? Math.sqrt(s / (n - 1)) : NaN;
}
function qSorted(sorted, p) {
  if (!sorted.length) return NaN;
  var pos = (sorted.length - 1) * p, lo = Math.floor(pos), hi = Math.ceil(pos);
  if (lo === hi) return sorted[lo];
  return sorted[lo] + (sorted[hi] - sorted[lo]) * (pos - lo);
}
/* MAD去极值 → 截面ZSCORE → 缺失填0（复刻 _winsor_z） */
function winsorZ(vals) {
  var n = vals.length, v = [], vi = [];
  for (var i = 0; i < n; i++) {
    var x = vals[i];
    if (x != null && isFinite(x)) { v.push(x); vi.push(i); }
  }
  var out = new Array(n);
  for (var j = 0; j < n; j++) out[j] = 0;
  if (v.length < 3) return out;
  var s = v.slice().sort(function (a, b) { return a - b; });
  var med = qSorted(s, 0.5);
  var mads = v.map(function (x) { return Math.abs(x - med); }).sort(function (a, b) { return a - b; });
  var mad = qSorted(mads, 0.5);
  if (mad > 0) {
    var lo = med - 3 * 1.4826 * mad, hi = med + 3 * 1.4826 * mad;
    for (var k = 0; k < v.length; k++) v[k] = Math.min(hi, Math.max(lo, v[k]));
  }
  var m = mean(v), sd = stdev(v);
  if (!(sd > 0)) return out;
  for (var t = 0; t < v.length; t++) out[vi[t]] = (v[t] - m) / sd;
  return out;
}
/* 平均秩（并列取均值，与 pandas rank 一致） */
function rankAvg(a) {
  var idx = [];
  for (var i = 0; i < a.length; i++) idx.push(i);
  idx.sort(function (x, y) { return a[x] - a[y]; });
  var r = new Array(a.length), i = 0;
  while (i < a.length) {
    var j = i;
    while (j + 1 < a.length && a[idx[j + 1]] === a[idx[i]]) j++;
    var rk = (i + j) / 2 + 1;
    for (var t = i; t <= j; t++) r[idx[t]] = rk;
    i = j + 1;
  }
  return r;
}
/* Spearman 秩相关（样本<10 → null，与生成器口径一致） */
function spearman(xs, ys) {
  var x = [], y = [];
  for (var i = 0; i < xs.length; i++) {
    if (xs[i] != null && isFinite(xs[i]) && ys[i] != null && isFinite(ys[i])) { x.push(xs[i]); y.push(ys[i]); }
  }
  if (x.length < 10) return null;
  var rx = rankAvg(x), ry = rankAvg(y), mx = mean(rx), my = mean(ry);
  var cov = 0, vx = 0, vy = 0;
  for (var k = 0; k < x.length; k++) {
    var dx = rx[k] - mx, dy = ry[k] - my;
    cov += dx * dy; vx += dx * dx; vy += dy * dy;
  }
  if (vx <= 0 || vy <= 0) return null;
  return cov / Math.sqrt(vx * vy);
}

/* ------------------------------ 表达式引擎 ------------------------------
 * 语法：字段名 数字 + - * / ^ ( ) log abs sqrt neg min max pow
 * 非法值（log≤0、除0、负数开方、缺失操作数）→ 该样本缺失
 * ---------------------------------------------------------------------- */
var FUNCS = {
  log: function (a) { return a > 0 ? Math.log(a) : null; },
  abs: function (a) { return Math.abs(a); },
  sqrt: function (a) { return a >= 0 ? Math.sqrt(a) : null; },
  neg: function (a) { return -a; },
  min: function (a, b) { return Math.min(a, b); },
  max: function (a, b) { return Math.max(a, b); },
  pow: function (a, b) { return Math.pow(a, b); }
};
function tokenize(src) {
  var toks = [], i = 0;
  while (i < src.length) {
    var c = src[i];
    if (/\s/.test(c)) { i++; continue; }
    if (/[0-9.]/.test(c)) {
      var num = '';
      while (i < src.length && /[0-9.]/.test(src[i])) num += src[i++];
      if ((num.match(/\./g) || []).length > 1 || num === '.') return { err: '非法数字 "' + num + '"' };
      toks.push({ t: 'num', v: parseFloat(num) });
      continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      var id = '';
      while (i < src.length && /[A-Za-z0-9_]/.test(src[i])) id += src[i++];
      toks.push({ t: 'id', v: id });
      continue;
    }
    if ('+-*/^(),'.indexOf(c) >= 0) { toks.push({ t: c }); i++; continue; }
    return { err: '非法字符 "' + c + '"' };
  }
  return { toks: toks };
}
function parseExpr(src) {
  if (exprCache[src]) return exprCache[src];
  var res = { ast: null, err: null };
  var tk = tokenize(src);
  if (tk.err) { res.err = tk.err; exprCache[src] = res; return res; }
  var toks = tk.toks, p = 0;
  function peek() { return toks[p]; }
  function eat(t) {
    if (toks[p] && toks[p].t === t) { p++; return true; }
    return false;
  }
  function parsePrimary() {
    var tok = peek();
    if (!tok) return { err: '表达式不完整' };
    if (tok.t === 'num') { p++; return { node: { k: 'num', v: tok.v } }; }
    if (tok.t === '(') {
      p++;
      var inner = parseExprNode();
      if (inner.err) return inner;
      if (!eat(')')) return { err: '缺少右括号 )' };
      return inner;
    }
    if (tok.t === 'id') {
      p++;
      if (eat('(')) {
        var args = [];
        if (!eat(')')) {
          for (;;) {
            var a = parseExprNode();
            if (a.err) return a;
            args.push(a.node);
            if (eat(',')) continue;
            if (eat(')')) break;
            return { err: '函数参数格式错误（应为 , 或 )）' };
          }
        }
        if (!FUNCS[tok.v]) return { err: '未知函数 ' + tok.v + '（可用：log abs sqrt neg min max pow）' };
        var arity = ['min','max','pow'].indexOf(tok.v) >= 0 ? 2 : 1;
        if (args.length !== arity) return { err: tok.v + ' 参数个数错误（需要 ' + arity + ' 个）' };
        return { node: { k: 'call', f: tok.v, args: args } };
      }
      return { node: { k: 'var', v: tok.v } };
    }
    return { err: '意外的符号 ' + tok.t };
  }
  function parseUnary() {
    if (eat('-')) {
      var inner = parseUnary();
      if (inner.err) return inner;
      return { node: { k: 'call', f: 'neg', args: [inner.node] } };
    }
    if (eat('+')) return parseUnary();
    return parsePrimary();
  }
  function parsePow() {
    var base = parseUnary();
    if (base.err) return base;
    if (eat('^')) {
      var exp = parsePow();
      if (exp.err) return exp;
      return { node: { k: 'call', f: 'pow', args: [base.node, exp.node] } };
    }
    return base;
  }
  function parseTerm() {
    var node = parsePow();
    if (node.err) return node;
    for (;;) {
      if (eat('*')) {
        var r = parsePow(); if (r.err) return r;
        node = { node: { k: 'op', o: '*', a: node.node, b: r.node } };
      } else if (eat('/')) {
        var r2 = parsePow(); if (r2.err) return r2;
        node = { node: { k: 'op', o: '/', a: node.node, b: r2.node } };
      } else return node;
    }
  }
  function parseExprNode() {
    var node = parseTerm();
    if (node.err) return node;
    for (;;) {
      if (eat('+')) {
        var r = parseTerm(); if (r.err) return r;
        node = { node: { k: 'op', o: '+', a: node.node, b: r.node } };
      } else if (eat('-')) {
        var r2 = parseTerm(); if (r2.err) return r2;
        node = { node: { k: 'op', o: '-', a: node.node, b: r2.node } };
      } else return node;
    }
  }
  var out = parseExprNode();
  if (out.err) { res.err = out.err; }
  else if (p < toks.length) { res.err = '表达式末尾有多余内容'; }
  else {
    // 静态检查：引用的变量必须是已知字段或自定义因子
    var used = {};
    (function walk(n) {
      if (n.k === 'var') used[n.v] = 1;
      else if (n.k === 'op') { walk(n.a); walk(n.b); }
      else if (n.k === 'call') n.args.forEach(walk);
    })(out.node);
    for (var key in used) {
      if (!(key in FIDX) && !isCustom(key)) {
        res.err = '未知字段 "' + key + '"（可在因子库查看全部字段名）';
        break;
      }
    }
    if (!res.err) { res.ast = out.node; res.used = used; }
  }
  exprCache[src] = res;
  return res;
}
function evalAst(node, getVal, stack) {
  switch (node.k) {
    case 'num': return node.v;
    case 'var': return getVal(node.v, stack || {});
    case 'op': {
      var a = evalAst(node.a, getVal, stack), b = evalAst(node.b, getVal, stack);
      if (a == null || b == null) return null;
      if (node.o === '+') return a + b;
      if (node.o === '-') return a - b;
      if (node.o === '*') return a * b;
      if (node.o === '/') return b === 0 ? null : a / b;
      return null;
    }
    case 'call': {
      var args = [];
      for (var i = 0; i < node.args.length; i++) {
        var v = evalAst(node.args[i], getVal, stack);
        if (v == null) return null;
        args.push(v);
      }
      var out = FUNCS[node.f].apply(null, args);
      return isFinite(out) ? out : null;
    }
  }
  return null;
}

/* ------------------------------ 因子取值 ------------------------------ */
function isCustom(key) { return key.indexOf(CUSTOM_KEYS) === 0; }
function customDef(key) {
  for (var i = 0; i < CFG.custom.length; i++) if (CFG.custom[i].key === key) return CFG.custom[i];
  return null;
}
/* 取一行某因子值（内置=row[3+FIDX]，自定义=递归求值） */
function rowFactor(row, key, stack) {
  if (key in FIDX) {
    var v = row[3 + FIDX[key]];
    return (v == null || !isFinite(v)) ? null : v;
  }
  var def = customDef(key);
  if (!def) return null;
  stack = stack || {};
  if (stack[key]) return null;  // 循环引用保护
  if (def.__cacheRow === row) return def.__cacheVal;
  stack[key] = 1;
  var val = evalAst(def.__ast, function (k, st) { return rowFactor(row, k, st); }, stack);
  stack[key] = 0;
  def.__cacheRow = row; def.__cacheVal = val;
  return val;
}
function fieldName(key) {
  if (key in FIDX) return FIELDS[FIDX[key]].n;
  var def = customDef(key);
  return def ? def.name : key;
}
function fieldDesc(key) {
  if (key in FIDX) return FIELDS[FIDX[key]].d;
  var def = customDef(key);
  return def ? (def.desc || '自创因子：' + def.expr) : '';
}
/* 因子方向（自定义因子默认+1，可改） */
function factorDir(key, gi) {
  var sel = CFG.sel[gi];
  for (var i = 0; i < sel.length; i++) if (sel[i].k === key) return sel[i].dir;
  var f = FIELDS[FIDX[key]];
  if (f && f.dir && f.dir[GROUPS[gi]] != null) return f.dir[GROUPS[gi]];
  return f && Number(f.direction_hint)===-1 ? -1 : 1;
}

/* ------------------------------ 配置管理 ------------------------------ */
function defaultCfg() {
  var sel = {};
  for (var g = 0; g < GROUPS.length; g++) {
    sel[g] = (DEFAULTS[GROUPS[g]] || []).map(function (p) { return { k: p[0], dir: p[1] }; });
  }
  return {
    sel: sel,
    custom: [],
    params: { topRatio: CONSTS.topRatio, turnover: false, turnoverLimit: 0.5, costBps: 5, mode: 'combo', allocationMode: 'initial_equal', start:D.period?.[0],end:D.period?.[1] }
  };
}
function compileCustoms() {
  for (var i = 0; i < CFG.custom.length; i++) {
    var c = CFG.custom[i];
    var r = parseExpr(c.expr);
    c.__ast = r.err ? null : r.ast;
    c.__err = r.err || null;
    c.__cacheRow = null; c.__cacheVal = null;
  }
}
function saveCfg() {
  LAST_BT = null; // A result always belongs to its frozen strategy, never edited controls.
  try {
    localStorage.setItem(LS_KEY, JSON.stringify({
      sel: CFG.sel, custom: CFG.custom.map(function (c) {
        return { key: c.key, name: c.name, expr: c.expr, desc: c.desc || '' };
      }), params: CFG.params
    }));
  } catch (e) { }
}
function loadCfg() {
  CFG = defaultCfg();
  try {
    var raw = localStorage.getItem(LS_KEY);
    if (!raw) return;
    var o = JSON.parse(raw);
    if (o && o.sel && o.custom && o.params) {
      CFG.sel = o.sel;
      CFG.custom = o.custom;
      CFG.params = Object.assign({},CFG.params,o.params);
    }
  } catch (e) { CFG = defaultCfg(); }
  compileCustoms();
}
function resetCfg() {
  CFG = defaultCfg();
  compileCustoms();
  saveCfg();
}
function cfgToJson() {
  var groups = {};
  for (var g = 0; g < GROUPS.length; g++) {
    groups[GROUPS[g]] = CFG.sel[g].map(function (p) { return { key: p.k, dir: p.dir }; });
  }
  return {
    version: 2,
    schema: "StrategySpec/mf/2",
    method_version: "mf-research/2.2-quality",
    research_assumptions: { settlement_mode: (D.market || {}).settlementMode || 'evidence_only',
                           credit_recovery: (D.market || {}).creditRecovery == null ? 1 : D.market.creditRecovery },
    data_version: D.metadata.data_version,
    code_version: D.metadata.code_version,
    code_sha256: D.metadata.code_sha256,
    source_sha256: D.metadata.source_sha256,
    accounting: D.metadata.contract,
    name: 'mf_lab_' + new Date().toISOString().slice(0, 10).replace(/-/g, ''),
    source: 'mf_lab_browser',
    created_at: new Date().toISOString(),
    period: selectedBacktestPeriod(),
    signal_calendar: {anchor_start:D.period?.[0],anchor_end:D.period?.[1],every_n_sessions:5},
    research_diagnostics: window.MFResearchUI?.getOptions?.()||null,
    custom_factors: CFG.custom.map(function (c) {
      return { key: c.key, name: c.name, expr: c.expr, desc: c.desc || '' };
    }),
    groups: groups,
    params: {
      top_ratio: CFG.params.topRatio,
      turnover_limit: CFG.params.turnover ? CFG.params.turnoverLimit : null,
      cost_per_side_bps: CFG.params.costBps,
      mode: CFG.params.mode === 'combo' ? 'combo' : GROUPS[Number(CFG.params.mode)],
      allocation_mode: CFG.params.allocationMode || 'initial_equal',
      turnover_definition: 'bilateral_actual_traded_value_over_pretrade_nav'
    }
  };
}

/* ------------------------------ 打分引擎 ------------------------------ */
/* 返回 null（组太小/无因子）或 {rows, scores, zdetail} */
function scoreGroup(week, gi) {
  var sel = CFG.sel[gi];
  if (!sel.length) return null;
  var rows = [];
  for (var i = 0; i < week.rows.length; i++) if (week.rows[i][1] === gi) rows.push(week.rows[i]);
  if (rows.length < CONSTS.minGroupSize) return null;
  var scores = new Array(rows.length), m = rows.length;
  for (var j = 0; j < m; j++) scores[j] = 0;
  var used = 0;
  for (var f = 0; f < sel.length; f++) {
    var key = sel[f].k, dir = sel[f].dir;
    var vals = new Array(m);
    var ok = true;
    for (var r = 0; r < m; r++) {
      var v = rowFactor(rows[r], key);
      if (v == null && isCustom(key)) { var def = customDef(key); if (def && def.__err) { ok = false; break; } }
      vals[r] = v;
    }
    if (!ok) return null;  // 自创因子表达式错误 → 该组本周无得分
    var z = winsorZ(vals);
    for (var r2 = 0; r2 < m; r2++) scores[r2] += dir * z[r2];
    used++;
  }
  if (!used) return null;
  for (var r3 = 0; r3 < m; r3++) scores[r3] /= used;
  return { rows: rows, scores: scores };
}

/* ------------------------------ IC 引擎 ------------------------------ */
function icStats(arr) {
  if (!arr.length) return null;
  var m = mean(arr), sd = stdev(arr);
  var pos = 0;
  for (var i = 0; i < arr.length; i++) if (arr[i] > 0) pos++;
  return {
    mean: m, icir: sd > 0 ? m / sd : null, pos: pos / arr.length,
    n: arr.length, t: sd > 0 ? m / sd * Math.sqrt(arr.length) : null
  };
}
/* 带日期的周度IC（供因子档案时序图与分年度统计） */
function icSeriesDated(gi, key) {
  var dates = [], ics = [];
  for (var k = 0; k < WEEKS.length; k++) {
    var w = WEEKS[k];
    if (w.e == null) continue;
    var rows = [], fwds = [];
    for (var i = 0; i < w.rows.length; i++) {
      var r = w.rows[i];
      if (r[1] !== gi) continue;
      if (r[2] == null) continue;
      rows.push(r); fwds.push(r[2]);
    }
    if (rows.length < 10) continue;
    var vals = rows.map(function (row) { return rowFactor(row, key); });
    var ic = spearman(vals, fwds);
    if (ic != null) { dates.push(w.d); ics.push(ic); }
  }
  return { dates: dates, ics: ics };
}
function icSeries(gi, key) { return icSeriesDated(gi, key).ics; }
/* 分年度IC统计 */
function yearlyICStats(dated) {
  var byYear = {}, order = [];
  for (var i = 0; i < dated.dates.length; i++) {
    var y = dated.dates[i].slice(0, 4);
    if (!byYear[y]) { byYear[y] = []; order.push(y); }
    byYear[y].push(dated.ics[i]);
  }
  order.sort();
  return order.map(function (y) {
    var a = byYear[y], pos = 0;
    for (var j = 0; j < a.length; j++) if (a[j] > 0) pos++;
    return { year: y, mean: mean(a), sd: stdev(a), pos: pos / a.length, n: a.length };
  });
}
/* 滚动均值 */
function rollMean(arr, win) {
  var out = [], s = 0;
  for (var i = 0; i < arr.length; i++) {
    s += arr[i];
    if (i >= win) s -= arr[i - win];
    out.push(s / Math.min(i + 1, win));
  }
  return out;
}
/* 最新有执行日的截面：当前组因子值分布 */
function latestGroupValues(gi, key) {
  for (var k = WEEKS.length - 1; k >= 0; k--) {
    var w = WEEKS[k];
    if (w.e == null) continue;
    var vals = [], pool = 0;
    for (var i = 0; i < w.rows.length; i++) {
      var r = w.rows[i];
      if (r[1] !== gi) continue;
      pool++;
      var v = rowFactor(r, key);
      if (v != null && isFinite(v)) vals.push(v);
    }
    if (vals.length >= 5) return { date: w.d, vals: vals, pool: pool };
  }
  return null;
}
function medianOf(arr) {
  var a = arr.slice().sort(function (x, y) { return x - y; });
  var n = a.length;
  if (!n) return null;
  return n % 2 ? a[(n - 1) / 2] : (a[n / 2 - 1] + a[n / 2]) / 2;
}
function quantileOf(arr, q) {
  var a = arr.slice().sort(function (x, y) { return x - y; });
  var pos = (a.length - 1) * q, lo = Math.floor(pos), hi = Math.ceil(pos);
  if (lo === hi) return a[lo];
  return a[lo] + (a[hi] - a[lo]) * (pos - lo);
}
/* 直方图 SVG（marks: [{v,label,color}] 竖线标注） */
function svgHist(title, values, opts) {
  opts = opts || {};
  var vals = values.filter(function (v) { return v != null && isFinite(v); });
  if (vals.length < 5) return '<div class="mf-sub">样本不足</div>';
  var bins = opts.bins || 26;
  var lo = Math.min.apply(null, vals), hi = Math.max.apply(null, vals);
  if (hi === lo) hi = lo + 1;
  var W = 920, H = 250, left = 58, right = W - 16, top = 36, bottom = H - 34;
  var counts = [];
  for (var b = 0; b < bins; b++) counts.push(0);
  vals.forEach(function (v) {
    var idx = Math.min(bins - 1, Math.floor((v - lo) / (hi - lo) * bins));
    counts[idx]++;
  });
  var cmax = Math.max.apply(null, counts);
  var p = [];
  p.push("<svg viewBox='0 0 " + W + " " + H + "' role='img' aria-label='" + esc(title) + "' class='mf-chart'>");
  p.push("<text x='" + left + "' y='16' font-size='12' fill='#475569'>" + esc(title) + "</text>");
  var bw = (right - left) / bins;
  for (var g = 0; g <= 2; g++) {
    var gy = top + (bottom - top) * g / 2;
    p.push("<line x1='" + left + "' y1='" + gy.toFixed(1) + "' x2='" + right + "' y2='" + gy.toFixed(1) + "' stroke='#eef0f4'/>");
    p.push("<text x='" + (left - 6) + "' y='" + (gy + 3.5).toFixed(1) + "' font-size='10' fill='#94a3b8' text-anchor='end'>" + (cmax * (1 - g / 2)).toFixed(0) + "</text>");
  }
  for (var i = 0; i < bins; i++) {
    var x = left + i * bw, hh = (bottom - top) * counts[i] / cmax;
    p.push("<rect x='" + (x + 0.6).toFixed(1) + "' y='" + (bottom - hh).toFixed(1) + "' width='" + Math.max(0.8, bw - 1.2).toFixed(1) + "' height='" + hh.toFixed(1) + "' fill='rgba(101,80,164,0.5)'/>");
  }
  (opts.marks || []).forEach(function (mk) {
    var mx = left + (mk.v - lo) / (hi - lo) * (right - left);
    if (mx < left || mx > right) return;
    p.push("<line x1='" + mx.toFixed(1) + "' y1='" + top + "' x2='" + mx.toFixed(1) + "' y2='" + bottom + "' stroke='" + (mk.color || '#b9922e') + "' stroke-width='1.6' stroke-dasharray='5,3'/>");
    p.push("<text x='" + Math.min(Math.max(mx, left + 44), right - 44).toFixed(1) + "' y='" + (top - 4) + "' font-size='10' fill='" + (mk.color || '#b9922e') + "' text-anchor='middle'>" + esc(mk.label) + "</text>");
  });
  for (var t = 0; t <= 4; t++) {
    var v = lo + (hi - lo) * t / 4;
    var tx = left + (right - left) * t / 4;
    p.push("<text x='" + tx.toFixed(1) + "' y='" + (bottom + 15) + "' font-size='10' fill='#94a3b8' text-anchor='" + (t === 0 ? 'start' : t === 4 ? 'end' : 'middle') + "'>" + (opts.fmt ? opts.fmt(v) : v.toFixed(2)) + "</text>");
  }
  p.push('</svg>');
  return p.join('');
}

/* ------------------------------ 因子档案文档（详细解释） ------------------------------ */
var FACTOR_DOCS = {
  price: {
    lg: '转债当日收盘价（元），最直接的绝对价格水平。',
    wh: '低价券（<115元）向下有债底与回售保护、向上保留期权弹性，"低价之谜"在转债市场长期存在；高价券（>130元）价格主要由正股驱动，波动放大。',
    use: '偏债/平衡型中常用方向 −1（价格越低保护越厚）；偏股型中价格已接近正股代理，单独使用区分度弱。',
    rk: '强赎博弈期的低价券可能因正股不涨而长期滞涨；信用冲击下债底下移，低价保护会失效。'
  },
  cb_value: {
    lg: '正股价 × 转股比例：立刻转股能换到的价值，股性锚。',
    wh: '平价决定转债的"股性底"——平价高则价格紧跟正股。平价本身不是选券因子，而是估值比较与动量计算的基准。',
    use: '一般不直接入模；作为平底溢价率、转股溢价率的分母，以及正股动量因子的载体（平价动量≈正股动量）。',
    rk: '下修会人为抬升平价；使用平价动量时已剔除窗内单日跳变>15%的样本。'
  },
  bond_value: {
    lg: '按同评级、同期限收益率对现金流折现得到的债底，债性锚。',
    wh: '底价是转债的债底支撑，底价占比高的券下行有限、定价由信用利差主导；偏债型组合的回撤基本由底价稳定性决定。',
    use: '不直接入模，是平底溢价率 / 纯债溢价率 / YTM 的计算基准。',
    rk: '折现曲线取最新评级快照近似，历史时点上评级下调会显著击穿估算底价。'
  },
  flat_prem: {
    lg: '平价 / 底价 − 1（%），股债属性相对强弱的度量，也是三分类的切分字段。',
    wh: '报告核心发现：同一因子在偏债与偏股券上反应相反，按平底溢价率分类后在类内选券，可避免跨类比较失真。',
    use: '本身即分类字段（<−20% 偏债、±20% 平衡、>20% 偏股）；也可作因子（值越高股性越强），但与分类信息重叠。',
    rk: '分类每周重划，边界券（±20%附近）在组间来回摆动会推高换手。'
  },
  ratio_pb: {
    lg: '平价与底价之比：平底溢价率的比值形式。',
    wh: '与 flat_prem 同源（比值 vs 差额），分布更对称，适合直接做截面排序。',
    use: '等价于按股性强弱排序；偏债型内取小值（纯债保护强）有区分度。',
    rk: '与 flat_prem 信息高度重叠，同组同时勾选相当于给股性维度双倍权重。'
  },
  prem: {
    lg: '价格 / 平价 − 1（%）：为期权与条款支付的成本。',
    wh: '溢价率低→转股阻力小、跟涨能力强；高溢价券依赖正股大涨或下修兑现，弹性打折。',
    use: '平衡/偏股型常用方向 −1（低溢价优先）；偏债型内溢价普遍偏高，截面区分度弱。',
    rk: '低溢价可能来自强赎预期或正股刚大跌；下修会造成溢价率跳变，破坏时序连续性。'
  },
  prem_z3: {
    lg: '溢价率相对自身过去63个交易日的时序ZSCORE。',
    wh: '捕捉"溢价率相对自己贵不贵"：Z 为负表示当前比近3月平均便宜，存在溢价修复空间；比原始溢价率更能适应不同价格中枢的券。',
    use: '三类均可用方向 −1（低Z=相对便宜）；与截面溢价率互补（一个看纵向、一个看横向）。',
    rk: '63日窗内若发生下修/强赎事件，Z值会被跳变污染；纯时序标准化不含截面信息。'
  },
  bond_prem: {
    lg: '价格 / 底价 − 1（%）：转债相对其债底的溢价。',
    wh: '衡量为期权支付了多少"债底以上"的成本；偏股型中该溢价低，说明转股价值支撑充分、下行缓冲好。',
    use: '偏股型常用方向 −1；偏债型内该值天然很小，区分度弱。',
    rk: '底价估算依赖评级曲线快照，信用事件期误差放大。'
  },
  ytm: {
    lg: '(110元到期赎回价 / 现价)^(1/剩余年限) − 1 的零息近似YTM。',
    wh: 'YTM 高=持有到期回报厚，是债底安全垫的价格化表达；高YTM组合在股市走弱期防御性强。',
    use: '平衡/偏股型方向 +1（报告默认用它捕捉组内防御性）；偏债型内YTM普遍高，区分度有限。',
    rk: '零息近似忽略期间票息，绝对值有偏差（截面排序基本保留）；临近到期/回售的券YTM会异常抬高。'
  },
  dual_low: {
    lg: '价格 + 转股溢价率：经典"双低"复合指标。',
    wh: '同时要求便宜（价格低）与跟涨能力强（溢价低），是转债市场流传最广的性价比指标。',
    use: '平衡/偏股型方向 −1（双低值越小越好）；偏债型内双低几乎退化为价格排序。',
    rk: '在高溢价低价券（妖券博弈）上会误判"便宜"；对信用风险完全不敏感。'
  },
  dl_z6: {
    lg: '双低相对自身过去126个交易日的时序ZSCORE。',
    wh: '把双低改成"相对自己近期是否变便宜"，剔除各券价格中枢差异后跨券可比。',
    use: '偏债/平衡型方向 −1；与截面双低互补使用。',
    rk: '126日窗跨越半年市况，风格切换期Z信号方向可能滞后。'
  },
  ratio_z3: {
    lg: '平价/底价的63日时序ZSCORE。',
    wh: '股债性比的边际变化：Z 低=相对近3月更偏债（防御状态），正股企稳时弹性修复空间大。',
    use: '偏债型方向 +1（报告默认：近期转股价值相对走高、尚未溢价的偏债券占优）。',
    rk: '逻辑依赖均值回归，单边杀股性的趋势行情中会持续反向。'
  },
  ratio_z6: {
    lg: '平价/底价的126日时序ZSCORE（半年窗口、更平滑）。',
    wh: '半年维度的股性摆动位置，信号更慢但更稳。',
    use: '平衡/偏股型方向 +1（股性处于半年高位且能维持的券动量延续）。',
    rk: '对快速V形反转反应慢；与 ratio_z3 高度相关，同组双勾近乎双倍权重。'
  },
  price_resid: {
    lg: '价格对平价的组内截面回归残差：同样平价的券，价格比同伴低多少。',
    wh: '剔除平价影响后的"截面相对便宜度"，比原始溢价率更纯粹的比价信号。',
    use: '平衡/偏股型方向 −1（残差低=相对同伴便宜）。',
    rk: '残差低也可能反映个体信用/条款折价（有原因的便宜），需结合评级与强赎状态。'
  },
  prem_resid: {
    lg: '溢价率对平价的组内截面回归残差。',
    wh: '高平价券溢价率天然低，回归残差剥离这一机械关系后，识别"溢价率异常高/低"的券。',
    use: '偏股型方向 −1（回归后溢价仍偏低的券跟涨阻力小）。',
    rk: '与 price_resid 信息重叠度较高（都是价格-平价截面关系）。'
  },
  r_cv20: {
    lg: '转股价值20日涨幅（窗内下修跳变剔除），即剔除下修扰动的正股动量。',
    wh: '转债收益最终由正股驱动，正股中期动量在偏股型内延续性较好。',
    use: '偏股/平衡型方向 +1；偏债型内正股动量对收益的解释力弱。',
    rk: '动量在情绪拐点（涨停潮后）反转剧烈；高动量券常已在价格高位，需与估值因子对冲使用。'
  },
  r_cb10: {
    lg: '转债自身近10个交易日涨幅。',
    wh: '转债价格短动量：资金关注度与追涨惯性的体现，短窗口上反转与延续并存。',
    use: '视市场状态可作 +1（惯性）或 −1（超跌反转），建议先在④IC验证再定向。',
    rk: '短动量因子IC通常不稳定，方向在不同年份间切换频繁。'
  },
  r_cb20: {
    lg: '转债自身近20个交易日涨幅（中期版本）。',
    wh: '比 r_cb10 更接近"趋势确认"，与正股动量（r_cv20）的相关性也更高。',
    use: '偏股型方向 +1；或作反转因子（−1）用于平衡型博弈超跌修复。',
    rk: '与 r_cv20 / diff10 相关性高，同组叠加会放大动量暴露。'
  },
  r120_z6: {
    lg: '平价120日涨幅的126日时序ZSCORE（下修剔除）。',
    wh: '正股半年维度的相对强弱，逐券标准化后比原始涨幅更适合跨券比较。',
    use: '平衡/偏股型方向 +1（报告默认：中期强正股的转债动量延续）。',
    rk: '半年动量在大级别风格切换（如成长↔价值）时会整体失效一次。'
  },
  diff10: {
    lg: '转债与正股10日涨幅之差（下修剔除），正=转债跑赢正股。',
    wh: '衡量转债估值的短期膨胀/收缩：转债持续跑赢正股=溢价被动抬升，后续有均值回归压力。',
    use: '偏债/平衡型方向 −1（报告默认：转债暂时跑输、溢价收缩后的券有修复空间）。',
    rk: '下修预案公告会造成"合法"的转债跑赢（转股价下调），剔除逻辑只覆盖已实施的跳变。'
  },
  diff10_z3: {
    lg: '涨幅差 diff10 的63日时序ZSCORE。',
    wh: '溢价摆动的标准化版本：Z 极端负=转债近3月明显跑输正股、溢价已压得很低。',
    use: '平衡型方向 −1（与 diff10 同逻辑但跨券可比）。',
    rk: '若正股持续阴跌，转债"跑输"其实是防御，信号会偏早，收益兑现要等正股企稳。'
  },
  boll120: {
    lg: '(平价 − MA120) / (2σ120)：正股在其半年布林带中的位置（±1为常规上下轨）。',
    wh: '超买超卖指标：接近 +1=正股短线过热，转债跟涨后可能回吐；接近 −1=超卖，有反弹博弈价值。',
    use: '平衡型方向 −1（报告默认：正股处于布林带下沿的转债超跌修复弹性大）。',
    rk: '强趋势中正股可沿上轨运行数月（指标钝化），反转逻辑失效。'
  },
  dist_high120: {
    lg: '平价 / 120日最高平价 − 1：距正股半年高点的位置（0=正创新高）。',
    wh: '类"距高点回撤"：贴近高点=正股强势维持、突破概率高（动量逻辑）；距高点深=深跌待修复（反转逻辑）。',
    use: '偏股型方向 +1（报告默认：贴近半年新高的正股动量最强）。',
    rk: '与 r120_z6 强相关；熊市里"贴近高点"的券突破失败率高。'
  },
  path_mom20: {
    lg: '−信息离散度：正股20日路径越平滑（连续小涨）值越大，大涨大跌交错则值小。',
    wh: '路径依赖效应：连续小涨的正股投资者盈利体验好、获利抛压小，动量延续性强；暴涨暴跌路径兑现压力大。',
    use: '平衡型方向 +1（报告默认：平滑上涨的正股动量质量高）。',
    rk: '构造较间接，低波动横盘样本区分度弱；窗内跳变剔除口径同动量类。'
  },
  turn120: {
    lg: '120个交易日累计换手率。',
    wh: '长期资金关注度：高换手=筹码交换充分、博弈激烈（常伴高溢价高波动）；低换手=机构持有型，走势温和。',
    use: '偏股型方向 −1（报告默认：低长期换手的偏股券更稳、回撤更小）。',
    rk: '低换手也意味着流动性差、冲击成本高，实盘需配合成交额过滤。'
  },
  turn_month: {
    lg: '21日累计换手率（样本池过滤字段之一：余额<2亿且近1月换手>100%的券剔除）。',
    wh: '短期交易拥挤度：近月换手暴增常对应题材炒作尾声，后续均值回归风险大。',
    use: '可作 −1 方向的拥挤度因子；在偏股型中与 turn120 互补（一个看长期、一个看近期）。',
    rk: '次新券上市初期换手天然偏高，样本池虽剔除上市≤2周券但余温仍在。'
  },
  turn5: {
    lg: '5日累计换手率：短期交易热度的最快探针。',
    wh: '捕捉资金脉冲：5日换手急升=游资进出、短线波动放大；静默券往往处于估值消化期。',
    use: '通常方向 −1（回避短期拥挤）；周度调仓下信号衰减快，IC稳定性一般。',
    rk: '极端值多（次新/妖券），MAD去极值后尾部信息被压缩。'
  },
  amount_avg3: {
    lg: '近3日平均成交额（千元），流动性规模的直接度量。',
    wh: '成交额决定可执行性与冲击成本；大体量资金应优先高成交额券，避免"回测买得到、实盘买不到"。',
    use: '常作流动性过滤而非收益因子；若入模，偏股型中高成交额常伴随高波动（方向不稳定）。',
    rk: '与"炒作热度"部分重叠，方向在样本期内不稳定，建议先做④IC验证。'
  },
  cb_vol20: {
    lg: '转债日收益率的20日标准差。',
    wh: '转债自身已实现波动：高波动券期权时间价值高但回撤也大；低波券适合防御底仓。',
    use: '视组合定位：防御型 +1（低波优先）或弹性型 −1；报告未列入默认因子。',
    rk: '波动率聚集效应强，急涨急跌后读数会持续偏高。'
  },
  cv_vol20: {
    lg: '转股价值日变化的20日标准差（下修剔除），即正股已实现波动。',
    wh: '正股波动是转债隐含波动率的锚：正股高波→期权更值钱→理应给更高溢价；残差视角可近似发现隐波错定价。',
    use: '可作 +1（高正股波动=高期权价值）或与溢价率组合成"隐波差"代理；本地无隐波数据，仅近似。',
    rk: '与 cb_vol20 高相关；波动率向收益的传导依赖市场定价效率。'
  },
  rem_years: {
    lg: '距到期日的年数。',
    wh: '期限决定期权时间价值与博弈节奏：剩余期限短→发行人还钱压力大，下修/拉抬促赎意愿强（到期博弈价值）；期限长→时间价值充裕但不确定性高。',
    use: '偏债型中"短期限+高YTM"是经典到期博弈组合；方向 ±1 均常见，视策略定位。',
    rk: '临近到期券流动性萎缩；到期赎回价按110元近似，与实际条款有差异。'
  },
  issue_size_yi: {
    lg: '发行规模（亿元），存量余额的点时代理。',
    wh: '小盘券易被资金撬动（高弹性高溢价高波动），大盘券走势贴近估值中枢；规模也决定机构可配置性。',
    use: '作 −1 因子（小盘超额）在弹性市中有效，但本质是流动性/博弈暴露而非价值因子。',
    rk: '用发行规模代理余额，未扣除转股/回售的余额衰减，长期误差累积；机构化行情中小盘因子反转。'
  }
};
/* 复合得分 IC（当前配置） */
function compositeICSeries(gi) {
  var out = [];
  for (var k = 0; k < WEEKS.length; k++) {
    var w = WEEKS[k];
    if (w.e == null) continue;
    var sc = scoreGroup(w, gi);
    if (!sc) continue;
    var fwds = [], scores = [];
    for (var i = 0; i < sc.rows.length; i++) {
      if (sc.rows[i][2] == null) continue;
      fwds.push(sc.rows[i][2]); scores.push(sc.scores[i]);
    }
    if (fwds.length < 10) continue;
    var ic = spearman(scores, fwds);
    if (ic != null) out.push(ic);
  }
  return out;
}

/* ------------------------------ 分层引擎 ------------------------------ */
/* 按因子值降序分5层，返回各层净值/年化/多空 */
function quintileAnalysis(gi, key) {
  var layers = [[], [], [], [], []];  // 每层周收益序列
  for (var k = 0; k < WEEKS.length; k++) {
    var w = WEEKS[k];
    if (w.e == null) continue;
    var rows = [];
    for (var i = 0; i < w.rows.length; i++) {
      var r = w.rows[i];
      if (r[1] !== gi || r[2] == null) continue;
      var v = rowFactor(r, key);
      if (v == null) continue;
      rows.push({ r: r, v: v });
    }
    if (rows.length < 10) continue;
    rows.sort(function (a, b) { return b.v - a.v; });
    var n = rows.length, per = n / 5;
    for (var q = 0; q < 5; q++) {
      var lo = Math.floor(q * per), hi = Math.floor((q + 1) * per);
      if (q === 4) hi = n;
      var sum = 0, cnt = 0;
      for (var j = lo; j < hi; j++) { sum += rows[j].r[2]; cnt++; }
      layers[q].push(cnt ? sum / cnt : 0);
    }
  }
  if (!layers[0].length) return null;
  var navs = [], anns = [];
  for (var q2 = 0; q2 < 5; q2++) {
    var nav = 1, arr = layers[q2];
    for (var t = 0; t < arr.length; t++) nav *= (1 + arr[t]);
    navs.push(nav);
    anns.push(Math.pow(nav, CONSTS.weeksPerYear / arr.length) - 1);
  }
  return { layers: layers, navs: navs, anns: anns, weeks: layers[0].length };
}

/* ------------------------------ 回测引擎 ------------------------------ */
function boundedTarget(target, current, limit) {
  var keys = Object.keys(Object.assign({}, target, current)).sort(), distance = 0;
  keys.forEach(function(c) { distance += Math.abs((target[c] || 0) - (current[c] || 0)); });
  if (limit != null && (!isFinite(limit) || limit < 0 || limit > 2)) throw Error('双边换手预算须在0至200%');
  var alpha = limit != null && distance > 0 ? Math.min(1, limit / distance) : 1, out = {};
  keys.forEach(function(c) { var v = (current[c] || 0) + alpha * ((target[c] || 0) - (current[c] || 0)); if (v > 1e-12) out[c] = v; });
  return out;
}
function desiredForWeek(w, groups) {
  var target = {}, scores = {};
  groups.forEach(function(gi) {
    var sc = scoreGroup(w, gi); if (!sc) return;
    var order = sc.rows.map(function(row,i) { return {bi:row[0], score:sc.scores[i]}; });
    order.sort(function(a,b) { return b.score-a.score || a.bi-b.bi; });
    var K = Math.max(1, Math.ceil(order.length * CFG.params.topRatio));
    order.slice(0,K).forEach(function(r) { target[r.bi] = (target[r.bi] || 0) + 1/K/groups.length; scores[r.bi]=r.score; });
  });
  return {target:target,scores:scores};
}
/* Observed marks are separate from volume-gated execution. Unverified recoveries stay locked. */
function mfRecordValuation(st, date) {
    st.unresolved_valuation = st.unresolved_valuation || [];
    st.valuation_events = st.valuation_events || [];
    const positions = {}, unresolved = [];
    Object.keys(st.units).sort().forEach(code => {
        const units = st.units[code]; if (!(units > 1e-12)) return;
        const observed = st.marks[code], price = typeof observed === 'number' && isFinite(observed) && observed > 0 ? observed : null;
        const recovery = (st.unresolvedSettlements || {})[code], missing = (st.quality || {})[code];
        const status = recovery ? recovery.status : missing ? 'missing_quote_locked_units_stale_valuation' : 'observed';
        const p = { code: BONDS[code] ? BONDS[code][0] : code, bi: Number(code), units: units, mark_price: price, mark_date: (st.markDates || {})[code] || null,
            value: price == null ? null : units * price, status: status };
        positions[code] = p; if (recovery || missing) unresolved.push(p);
    });
    const nav = st.cash + Object.values(positions).reduce((v, p) => v + (p.value || 0), 0);
    const amount = unresolved.reduce((v, p) => v + (p.value || 0), 0);
    const row = { date: date, nav: nav, cash: st.cash, unresolved_value: amount,
        unresolved_nav_share: nav > 0 ? amount / nav : null, unresolved_count: unresolved.length };
    st.unresolved_valuation.push(row);
    const signature = JSON.stringify(unresolved);
    if (signature !== (st._valuationSignature || '[]')) {
        st.valuation_events.push({ date: date, positions: unresolved }); st._valuationSignature = signature;
    }
    st.end_positions = positions;
    const previous = st.unresolved_summary || {};
    st.unresolved_summary = { end_value: amount, end_share: row.unresolved_nav_share,
        max_value: Math.max(previous.max_value || 0, amount),
        max_share: row.unresolved_nav_share == null ? previous.max_share || null : Math.max(previous.max_share || 0, row.unresolved_nav_share),
        unresolved_days: (previous.unresolved_days || 0) + (unresolved.length ? 1 : 0), end_count: unresolved.length,
        measurement: 'last_observed_mark; securities, not cash' };
    st.valuation_sensitivity = { qualification: 'valuation_scenario_only; no actual settlement or cash flow',
        basis: 'haircut unresolved last-observed market value at the endpoint', cash_unchanged: st.cash,
        scenarios: [0, 0.5, 1].map(ratio => ({ mark_recovery_ratio: ratio, end_mark_adjusted_nav: nav - (1 - ratio) * amount })) };
}
function mfValuationSnapshot(st) {
    return JSON.parse(JSON.stringify({ quality_contract_version: 'research-quality/1',
        valuation_units: { value_unit: 'initial_nav_1', quantity_unit: 'normalized_initial_capital/quote_price',
            note: 'model quantities; not account currency or actual bond lots' },
        valuation_audit_scope: { start: (st.unresolved_valuation || [])[0]?.date || null,
            end: (st.unresolved_valuation || []).at(-1)?.date || null,
            end_positions_date: (st.unresolved_valuation || []).at(-1)?.date || null },
        unresolved_valuation: st.unresolved_valuation || [], valuation_events: st.valuation_events || [],
        end_positions: st.end_positions || {}, unresolved_summary: st.unresolved_summary || {},
        valuation_sensitivity: st.valuation_sensitivity || {} }));
}
function mfCombineValuation(sleeves, groups) {
  var n=sleeves.length,out={unresolved_valuation:[],valuation_events:[],end_positions:{}},byDate={},events={},active={};
  sleeves.forEach(function(s,i){var group=groups[i];
    (s.unresolved_valuation||[]).forEach(function(r){(byDate[r.date]||(byDate[r.date]=[])).push(r);});
    (s.valuation_events||[]).forEach(function(e){(events[e.date]||(events[e.date]=[])).push({group:group,positions:e.positions});});
    Object.keys(s.end_positions||{}).forEach(function(c){var p=s.end_positions[c];out.end_positions[group+':'+c]=Object.assign({},p,{sleeve:group,units:p.units/n,value:p.value==null?null:p.value/n});});
  });
  Object.keys(byDate).sort().forEach(function(day){var rows=byDate[day],nav=rows.reduce(function(v,r){return v+r.nav;},0)/n,amount=rows.reduce(function(v,r){return v+r.unresolved_value;},0)/n;
    out.unresolved_valuation.push({date:day,nav:nav,cash:rows.reduce(function(v,r){return v+r.cash;},0)/n,unresolved_value:amount,unresolved_nav_share:nav>0?amount/nav:null,unresolved_count:rows.reduce(function(v,r){return v+r.unresolved_count;},0)});
    if(events[day]){events[day].forEach(function(e){active[e.group]=e.positions.map(function(p){return Object.assign({},p,{sleeve:e.group,units:p.units/n,value:p.value==null?null:p.value/n});});});out.valuation_events.push({date:day,positions:Object.keys(active).sort().flatMap(function(g){return active[g];})});}
  });
  var rows=out.unresolved_valuation,end=rows[rows.length-1]||{},shares=rows.map(function(r){return r.unresolved_nav_share;}).filter(function(v){return v!=null;});
  out.unresolved_summary={end_value:end.unresolved_value||0,end_share:end.unresolved_nav_share==null?null:end.unresolved_nav_share,max_value:rows.length?Math.max.apply(null,rows.map(function(r){return r.unresolved_value;})):0,max_share:shares.length?Math.max.apply(null,shares):null,unresolved_days:rows.filter(function(r){return r.unresolved_count>0;}).length,end_count:end.unresolved_count||0,measurement:'last_observed_mark; securities, not cash'};
  out.valuation_sensitivity={qualification:'valuation_scenario_only; no actual settlement or cash flow',basis:'haircut unresolved last-observed market value at the endpoint',cash_unchanged:end.cash,scenarios:[0,.5,1].map(function(r){return {mark_recovery_ratio:r,end_mark_adjusted_nav:(end.nav||0)-(1-r)*(end.unresolved_value||0)};})};
  return mfValuationSnapshot(out);
}

// 实时策略研究：T+1执行；缺价只影响成交，不提前改变信号截面。
function runPortfolio(groups) {
  if (!D.market || D.v < 2) throw Error('数据版本过旧：须重新生成v2日行情载荷');
  var range=selectedBacktestPeriod(),frames=D.market.frames;
  var endFrame=frames.filter(function(f){return f.d<=range[1];}).at(-1);
  var periods = WEEKS.filter(function(w) { return w.d>=range[0]&&w.d<=range[1]&&w.e&&endFrame&&w.e<endFrame.d&&w.holding_end&&w.holding_end>w.e; }).map(function(w){return Object.assign({},w,{holding_end:w.holding_end>endFrame.d?endFrame.d:w.holding_end});});
  if (!periods.length) throw Error('没有完整的执行持有区间');
  var bySignal = {}; periods.forEach(function(w) { bySignal[w.d] = w; });
  var cash=1, units={}, marks={}, markDates={}, valuationAccount={}, pending=null, daily={}, beforeByDate={}, executions={}, issues={}, settlements=[], unresolvedSettlements={};
  var rate=CFG.params.costBps/1e4, limit=CFG.params.turnover ? CFG.params.turnoverLimit : null;
  var delist=D.market.delist||null, recovery=typeof D.market.creditRecovery==='number'?D.market.creditRecovery:1;
  var settlementMode=D.market.settlementMode||'evidence_only';
  var end=periods[periods.length-1].holding_end;
  function value() { var v=cash; Object.keys(units).forEach(function(c) { v+=units[c]*marks[c]; }); return v; }
  for (var di=0;di<frames.length;di++) {
    var frame=frames[di], day=frame.d; if (day<periods[0].d)continue;if (day>end) break;
    if (delist) Object.keys(units).sort(function(a,b){return a-b;}).forEach(function(c) {
      var rule=delist[c]; if (!rule || rule[0]>day) return;
      var last=marks[c], lastOk=isFinite(last)&&last>0, px=null;
      var verified=rule[5]===true && typeof rule[2]==='number'&&isFinite(rule[2])&&rule[2]>0 && !!rule[3] && !!rule[4];
      var legacy=settlementMode==='legacy_last_price';
      var status=verified&&day<rule[3]?'pending_payment':verified?'verified_payment':legacy?'assumed_last_price':'unverified_recovery';
      var audit={status:status,mode:settlementMode,payment_date:verified?rule[3]:null,payment_evidence:verified?rule[4]:null,strict_pit:false};
      if ((!verified&&!legacy)||(verified&&day<rule[3])) { unresolvedSettlements[c]=Object.assign({date:day,last_close:last,kind:rule[1]},audit); return; }
      if (verified) px=rule[2];
      else if (rule[1]==='maturity') px=(typeof rule[2]==='number'&&isFinite(rule[2])&&rule[2]>0)?rule[2]:(lastOk?last:null);
      else if (lastOk) px=rule[1]==='abnormal'?last*recovery:last;
      if (px==null) return;
      var gross=units[c]*px, fee=verified||rule[1]==='maturity'?0:gross*rate;
      cash+=gross-fee; settlements.push(Object.assign({bi:Number(c),date:day,kind:rule[1],settle_price:px,proceeds:gross-fee,fee:fee},audit));
      delete units[c]; delete marks[c]; delete markDates[c];
      delete unresolvedSettlements[c];
    });
    var quotes={}; frame.q.forEach(function(q) { quotes[q[0]]=q; });
    if (delist) Object.keys(quotes).forEach(function(c) { if (delist[c]&&delist[c][0]<=day) delete quotes[c]; });
    Object.keys(units).forEach(function(c) {
      if (quotes[c]) { marks[c]=quotes[c][1]; markDates[c]=day; }
      else { if (!issues[c]) issues[c]={code:BONDS[c][0],first_missing:day,last_missing:day,days:0}; issues[c].last_missing=day; issues[c].days++; }
    });
    beforeByDate[day]=value();
    if (pending) {
      var before=value(), current={}; Object.keys(units).forEach(function(c) { current[c]=units[c]*marks[c]/before; });
      var desired=pending.target, target=boundedTarget(desired,current,limit), traded=0, fees=0, orders=[];
      Object.keys(units).sort(function(a,b){return a-b;}).forEach(function(c) {
        var requested=units[c]*marks[c]-(target[c]||0)*before;
        if (requested<=1e-12) return;
        if (!quotes[c] || !quotes[c][2]) { orders.push({bi:Number(c),side:'sell',status:'unfilled',reason:'no_tradeable_quote'}); return; }
        var amount=Math.min(requested,units[c]*marks[c]),fee=amount*rate;
        units[c]-=amount/marks[c]; cash+=amount-fee; traded+=amount; fees+=fee;
        orders.push({bi:Number(c),side:'sell',status:'filled',value:amount,fee:fee});
      });
      Object.keys(units).forEach(function(c) { if (units[c]<=1e-12) delete units[c]; });
      var buys={}, totalBuy=0;
      Object.keys(target).forEach(function(c) {
        var requested=target[c]*before-(units[c]||0)*(marks[c]||0);
        if (requested<=1e-12) return;
        if (!quotes[c] || !quotes[c][2]) { orders.push({bi:Number(c),side:'buy',status:'unfilled',reason:'no_tradeable_quote'}); return; }
        buys[c]=requested; totalBuy+=requested;
      });
      var scale=totalBuy ? Math.min(1,Math.max(0,cash)/(totalBuy*(1+rate))) : 0;
      Object.keys(buys).sort(function(a,b){return a-b;}).forEach(function(c) {
        var amount=buys[c]*scale,fee=amount*rate,px=quotes[c][1];
        if (amount<=1e-12) { orders.push({bi:Number(c),side:'buy',status:'unfilled',reason:'insufficient_cash'}); return; }
        units[c]=(units[c]||0)+amount/px; marks[c]=px; markDates[c]=day; cash-=amount+fee; traded+=amount; fees+=fee;
        orders.push({bi:Number(c),side:'buy',status:scale>=1-1e-12?'filled':'partial',value:amount,fee:fee});
      });
      if (cash < -1e-10) throw Error('现金守恒失败'); cash=Math.max(0,cash);
      var bilateral=before>0?traded/before:0; if (limit!=null && bilateral>limit+1e-9) throw Error('实际成交超过换手预算');
      var after=value(), hold={d:pending.week.d,e:day,group:groups.length===1?groups[0]:-1,list:[]};
      Object.keys(units).forEach(function(c) { hold.list.push({bi:Number(c),w:units[c]*marks[c]/after,score:pending.scores[c]==null?null:pending.scores[c]}); });
      executions[day]={nav_before:before,nav_after:after,bilateral_turnover:bilateral,fees:fees,cash:cash,
                       orders:orders,target:desired,budgeted_target:target,hold:hold};
      pending=null;
    }
    if (bySignal[day]) { pending=desiredForWeek(bySignal[day],groups); pending.week=bySignal[day]; }
    daily[day]=value();
    var currentMissing={};Object.keys(units).forEach(function(c){if(!quotes[c])currentMissing[c]={status:'missing_quote_locked_units_stale_valuation'};});
    Object.assign(valuationAccount,{cash:cash,units:units,marks:marks,markDates:markDates,quality:currentMissing,unresolvedSettlements:unresolvedSettlements});
    mfRecordValuation(valuationAccount,day);
  }
  var navs=[daily[periods[0].d]], dates=[periods[0].d], rets=[], turnovers=[], holdings=[];
  periods.forEach(function(w) {
    var v=beforeByDate[w.holding_end], prev=navs[navs.length-1], ex=executions[w.e];
    if (!isFinite(v) || !ex) throw Error('行情或执行日缺失：'+w.e);
    navs.push(v); dates.push(w.holding_end); rets.push(v/prev-1);
    turnovers.push(ex.bilateral_turnover); holdings.push(ex.hold);
  });
  return {navs:navs,dates:dates,rets:rets,turnovers:turnovers,holdings:holdings,weeks:periods,
          executions:executions,daily:daily,issues:Object.keys(issues).map(function(c){return issues[c];}),
          settlements:settlements,unresolvedSettlements:unresolvedSettlements,finalCash:cash,finalUnits:units,
          ...mfValuationSnapshot(valuationAccount)};
}
function runSleeve(gi) { return runPortfolio([gi]); }
function selectedBacktestPeriod(){
  var frames=D.market?.frames||[],available=D.period||[frames[0]?.d,frames.at(-1)?.d];
  var start=CFG.params.start||available[0],end=CFG.params.end||available[1];
  if(!start||!end||start>end)throw Error('回测开始日必须早于结束日');
  if(start<available[0]||end>available[1])throw Error('回测日期超出当前数据范围 '+available.join(' 至 '));
  return [start,end];
}
function runBacktest() {
  var t0=Date.now(), modeGroups=CFG.params.mode==='combo' ? GROUPS.map(function(_,i){return i;}) : [Number(CFG.params.mode)];
  var sleeves=modeGroups.map(runSleeve), portfolio, allocation=CFG.params.allocationMode || 'initial_equal';
  if (modeGroups.length===1) portfolio=sleeves[0];
  else if (allocation==='weekly_equal') portfolio=runPortfolio(modeGroups);
  else {
    var base=sleeves[0], navs=base.navs.map(function(_,k){return mean(sleeves.map(function(r){return r.navs[k];}));});
    var daily={}; Object.keys(base.daily).forEach(function(d){daily[d]=mean(sleeves.map(function(r){return r.daily[d];}));});
    var turnovers=base.weeks.map(function(w){
      var before=0,trade=0; sleeves.forEach(function(r){var e=r.executions[w.e];before+=e.nav_before;trade+=e.nav_before*e.bilateral_turnover;});
      return before?trade/before:0;
    });
    portfolio={navs:navs,dates:base.dates,rets:navs.slice(1).map(function(v,i){return v/navs[i]-1;}),turnovers:turnovers,daily:daily,
               weeks:base.weeks,issues:[].concat.apply([],sleeves.map(function(r){return r.issues;})),
               settlements:[].concat.apply([],sleeves.map(function(r){return r.settlements||[];})),
               unresolvedSettlements:Object.assign.apply(Object,[{}].concat(sleeves.map(function(r,i){
                 var out={};Object.keys(r.unresolvedSettlements||{}).forEach(function(c){out[i+':'+c]=r.unresolvedSettlements[c];});return out;
               })))};
    Object.assign(portfolio,mfCombineValuation(sleeves,modeGroups.map(function(i){return GROUPS[i];})));
  }
  var dates=portfolio.dates, prices=D.indexPrices || {}, firstDate=dates.find(function(d){return typeof prices[d]==='number'&&isFinite(prices[d])&&prices[d]>0;}),first=prices[firstDate],idx=dates.map(function(d){return first && typeof prices[d]==='number'&&isFinite(prices[d])&&prices[d]>0?prices[d]/first:null;});
  var dailyDates=Object.keys(portfolio.daily).sort();
  var dailyValues=dailyDates.map(function(d){return portfolio.daily[d];});
  var dailyIndex=dailyDates.map(function(d){return prices[d]==null?null:prices[d];});
  var benchmarkQuality=mfBenchmarkQuality(dailyDates,dailyIndex);
  var metrics=computeMetrics(dailyValues,portfolio.rets);
  var accounts;
  if (modeGroups.length===1 || allocation==='weekly_equal') accounts=[portfolio];
  else accounts=[{holdings:sleeves[0].weeks.map(function(w,k){
    var total=0, combined={};sleeves.forEach(function(sl){total+=sl.executions[w.e].nav_after;});
    sleeves.forEach(function(sl){var share=sl.executions[w.e].nav_after/total;sl.holdings[k].list.forEach(function(x){
      if(!combined[x.bi])combined[x.bi]={bi:x.bi,w:0,score:x.score};combined[x.bi].w+=x.w*share;
    });});return {d:w.d,e:w.e,group:-1,list:Object.keys(combined).map(function(c){return combined[c];})};
  })}];
  LAST_BT={combo:portfolio.navs,rets:portfolio.rets,turnovers:portfolio.turnovers,dates:dates,idx:idx,
    sleeves:sleeves,accounts:accounts,modeGroups:modeGroups,ms:Date.now()-t0,metrics:metrics,
    idxMetrics:benchmarkQuality.complete?computeMetrics(dailyIndex,idx.slice(1).map(function(v,i){return v==null||idx[i]==null?NaN:v/idx[i]-1;})):{},
    benchmark_quality:benchmarkQuality,
    ...mfValuationSnapshot(portfolio),
    daily:portfolio.daily,issues:portfolio.issues,settlements:portfolio.settlements||[],unresolvedSettlements:portfolio.unresolvedSettlements||{},
    metadata:{method_version:'mf-research/2.2-quality',data_version:D.metadata.data_version,code_version:D.metadata.code_version,
              run_id:'mf-'+Date.now().toString(36),allocation_mode:allocation,
              accounting:D.metadata.contract,strict_pit:false,limitations:D.metadata.limitations},
    strategy:cfgToJson()};
  LAST_BT.yearly = yearlyTable(LAST_BT);
  return LAST_BT;
}
function mfBenchmarkQuality(dates, raw) {
    const missing = [], ranges = []; let observed = 0, active = null;
    dates.forEach((date, i) => {
        const value = raw[i], valid = typeof value === 'number' && isFinite(value) && value > 0;
        if (!valid) { missing.push(date); active = null; return; }
        observed++;
        if (!active) { active = { start: date, end: date, points: 0 }; ranges.push(active); }
        active.end = date; active.points++;
    });
    const complete = dates.length > 0 && raw.length === dates.length && observed === dates.length;
    return { contract_version: 'research-quality/1', status: complete ? 'complete' : observed ? 'partial' : 'missing',
        expected_points: dates.length, observed_points: observed, coverage: dates.length ? observed / dates.length : null,
        missing_dates: missing, first_valid_date: ranges.length ? ranges[0].start : null,
        last_valid_date: ranges.length ? ranges[ranges.length - 1].end : null, valid_ranges: ranges,
        complete: complete, fill_policy: 'observations_only; no forward/backward fill' };
}
function mfBenchmarkComplete(dates, raw) {
    return mfBenchmarkQuality(dates, raw).complete;
}
function mfSafeExcess(strategy, benchmark, quality) {
    return (!quality || quality.complete) && typeof strategy === 'number' && isFinite(strategy) &&
        typeof benchmark === 'number' && isFinite(benchmark) ? strategy - benchmark : null;
}

function computeMetrics(nav, rets) {
  // Daily risk/annualization agrees with Python. Weekly hit-rate remains a
  // separately labelled diagnostic of the execution-to-execution periods.
  if (!nav || nav.length < 3 || nav.some(function(v){return v==null||!isFinite(v)||v<=0;})) return {};
  var dailyReturns=nav.slice(1).map(function(v,i){return v/nav[i]-1;});
  var total = nav[nav.length - 1] / nav[0] - 1;
  var ann = Math.pow(1 + total, 252 / dailyReturns.length) - 1;
  var vol = stdev(dailyReturns) * Math.sqrt(252);
  var mdd = 0, peak = nav[0];
  for (var i = 0; i < nav.length; i++) {
    if (nav[i] > peak) peak = nav[i];
    var dd = nav[i] / peak - 1;
    if (dd < mdd) mdd = dd;
  }
  var wins = 0, losses = 0, sumW = 0, sumL = 0;
  for (var j = 0; j < rets.length; j++) {
    if (rets[j] > 0) { wins++; sumW += rets[j]; }
    else if (rets[j] < 0) { losses++; sumL += rets[j]; }
  }
  var sharpe = vol > 0 ? (mean(dailyReturns)*252 - CONSTS.rf) / vol : null;
  return {
    total: total, ann: ann, vol: vol, mdd: mdd, sharpe: sharpe,
    winRate: rets.length ? wins / rets.length : null,
    pl: (losses && sumL) ? (sumW / wins) / (-sumL / losses) : null,
    calmar: mdd < 0 ? ann / -mdd : null,
    weeks: rets.length, tradingDays:dailyReturns.length, annualizationDays:252
  };
}
function yearlyTable(bt) {
  var rows = {}, order=[], dailyDates=Object.keys(bt.daily).sort(), prices=D.indexPrices||{};
  dailyDates.forEach(function(d,i){
    var y=d.slice(0,4),base=i>0?i-1:i;
    if(!rows[y]){order.push(y);rows[y]={rets:[],path:base<i?[bt.daily[dailyDates[base]]]:[],dates:base<i?[dailyDates[base]]:[],index:base<i?[prices[dailyDates[base]]]:[]};}
    rows[y].path.push(bt.daily[d]);rows[y].dates.push(d);rows[y].index.push(prices[d]);
  });
  for (var k = 0; k < bt.rets.length; k++) {
    var ds = bt.dates[k + 1] || '';
    var y = ds ? ds.slice(0, 4) : '?';
    if(rows[y]) rows[y].rets.push(bt.rets[k]);
  }
  var out = [];
  for (var i = 0; i < order.length; i++) {
    var y = order[i], r = rows[y];
    var quality=mfBenchmarkQuality(r.dates,r.index);
    var yr = r.path[r.path.length-1] / r.path[0] - 1, yi = quality.complete?r.index.at(-1)/r.index[0]-1:null;
    var m = computeMetrics(r.path, r.rets);
    out.push({
      year: y, ret: yr, idx: yi, excess: mfSafeExcess(yr,yi,quality), mdd: m.mdd,
      winRate: m.winRate, weeks: r.rets.length, benchmark_quality:quality
    });
  }
  return out;
}

/* ------------------------------ SVG 图表 ------------------------------ */
var PALETTE = ['#b91c1c', '#1f3a63', '#b9922e', '#0f766e', '#6550a4', '#94a3b8', '#be185d', '#4d7c0f'];
function svgLine(title, series, opts) {
  opts = opts || {};
  var W = opts.width || 920, H = opts.height || 330;
  var left = 58, right = W - 16, top = 42, bottom = H - 30;
  var all = [];
  for (var i = 0; i < series.length; i++) {
    for (var j = 0; j < series[i].values.length; j++) {
      var v = series[i].values[j];
      if (v != null && isFinite(v)) all.push(v);
    }
  }
  if (all.length < 2) return '<div class="mf-sub">暂无数据</div>';
  var ymin = Math.min.apply(null, all), ymax = Math.max.apply(null, all);
  var pad = (ymax - ymin) * 0.06 || 0.05;
  ymin -= pad; ymax += pad;
  var n = Math.max.apply(null, series.map(function (s) { return s.values.length; }));
  var step = Math.max(1, Math.floor(n / 600));
  function X(i) { return left + (right - left) * i / (n - 1); }
  function Y(v) { return bottom - (bottom - top) * (v - ymin) / (ymax - ymin); }
  var p = [];
  p.push("<svg viewBox='0 0 " + W + " " + H + "' role='img' aria-label='" + esc(title) + "' class='mf-chart'>");
  p.push("<text x='" + left + "' y='16' font-size='12' fill='#475569'>" + esc(title) + "</text>");
  var lx = left;
  for (var s = 0; s < series.length; s++) {
    if (!series[s].label) continue;
    p.push("<line x1='" + lx + "' y1='28' x2='" + (lx + 16) + "' y2='28' stroke='" + series[s].color + "' stroke-width='2.5'/>");
    var lbl = series[s].label.length > 26 ? series[s].label.slice(0, 25) + '…' : series[s].label;
    p.push("<text x='" + (lx + 20) + "' y='31.5' font-size='10.5' fill='#475569'>" + esc(lbl) + "</text>");
    lx += 26 + lbl.length * 10.5 + (series[s].endLabel ? 52 : 0);
  }
  for (var g = 0; g <= 4; g++) {
    var gy = top + (bottom - top) * g / 4, val = ymax - (ymax - ymin) * g / 4;
    p.push("<line x1='" + left + "' y1='" + gy.toFixed(1) + "' x2='" + right + "' y2='" + gy.toFixed(1) + "' stroke='#eef0f4'/>");
    p.push("<text x='" + (left - 6) + "' y='" + (gy + 3.5).toFixed(1) + "' font-size='10' fill='#94a3b8' text-anchor='end'>" + val.toFixed(2) + "</text>");
  }
  var ds = opts.dates || [];
  for (var m2 = 0; m2 < 3; m2++) {
    var frac = m2 === 0 ? 0 : (m2 === 1 ? 0.5 : 1);
    var di = ds[Math.min(Math.floor(frac * (n - 1)), ds.length - 1)] || '';
    var anchor = m2 === 0 ? 'start' : (m2 === 1 ? 'middle' : 'end');
    var px = m2 === 0 ? left : (m2 === 1 ? (left + right) / 2 : right);
    p.push("<text x='" + px.toFixed(0) + "' y='" + (H - 8) + "' font-size='10' fill='#94a3b8' text-anchor='" + anchor + "'>" + esc(di) + "</text>");
  }
  for (var s2 = 0; s2 < series.length; s2++) {
    var pts = [];
    for (var i2 = 0; i2 < series[s2].values.length; i2 += step) {
      var v2 = series[s2].values[i2];
      if (v2 != null && isFinite(v2)) pts.push(X(i2).toFixed(1) + ',' + Y(v2).toFixed(1));
    }
    var lastV = series[s2].values[series[s2].values.length - 1];
    p.push("<polyline points='" + pts.join(' ') + "' fill='none' stroke='" + series[s2].color + "' stroke-width='" + (series[s2].width || 2) + "' stroke-linejoin='round'/>");
    if (series[s2].endLabel && lastV != null) {
      p.push("<text x='" + (right - 2) + "' y='" + (Y(lastV) - 4).toFixed(1) + "' font-size='9.5' fill='" + series[s2].color + "' text-anchor='end'>" + esc(series[s2].endLabel) + "</text>");
    }
  }
  p.push('</svg>');
  return p.join('');
}
function icColor(v) {
  if (v == null || !isFinite(v)) return '#e5e7eb';
  var a = Math.min(Math.abs(v) / 0.10, 1) * 0.75 + 0.12;
  return v >= 0 ? 'rgba(185,28,28,' + a.toFixed(2) + ')' : 'rgba(31,58,99,' + a.toFixed(2) + ')';
}

/* ------------------------------ 视图：① 方法思路 ------------------------------ */
function vMethod() {
  var root = $('mf-view-method');
  clear(root);
  var card = h('div', 'mf-card');
  card.appendChild(h('h3', null, '研究思路：分类型多因子框架'));
  card.appendChild(h('p', 'mf-sub', '同风格转债对同一因子的反应不同（偏债看债底安全边际，偏股看正股动量），因此先分类、再在类内打分，避免跨类比较失真。'));
  var steps = [
    ['第1步 · 三分类', '平底溢价率 = 平价 / 底价 − 1。< -20% 为偏债型（' + CONSTS.flatDebt + '%阈值），±20% 为平衡型，> 20% 为偏股型（' + CONSTS.flatEquity + '%阈值）。每周信号日按当日值重新分类。'],
    ['第2步 · 样本池过滤', '样本池已预过滤：上市不足14个自然日、信号日存续余额<2亿元且21日换手代理>100%、信号日主体评级不在A及以上白名单、已记录强赎公告等。当前多因子池的近3日成交额门槛为0，不套用普通策略的1000万元门槛；执行日仍需正成交量。余额为转股结果公告的时点存续余额（不含回售），评级为通联主体评级调整事件重建的时点评级；换手代理的分母仍是发行规模；研究页的“全体”指通过这些过滤的转债。'],
    ['第3步 · 选因子', '从 '+FIELDS.length+' 个可计算字段中挑选因子并事先指定方向。在①选择时间区间和收益周期做验证，在②配置组合；窗口变体不能视作独立证据。'],
    ['第4步 · 数据处理', '组内截面：MAD去极值（中位数 ± 3×1.4826×MAD）→ ZSCORE标准化 → 缺失填0（等价于截面均值对应的Z=0替代）。'],
    ['第5步 · 打分与选券', '复合得分 = 所选因子（方向×Z）的等权平均；每类取得分前 ' + Math.round(CONSTS.topRatio * 100) + '% 构建多头组，组内等权。可选控换手（换手预算内优先保留旧持仓）。'],
    ['第6步 · 回测与复核', '信号日收盘出信号 → T+1 收盘成交，双边成本 ' + (CFG.params.costBps) + 'bp/边。浏览器逐日维护数量/现金，周度采样展示；⑥导出冻结数据版本与配置，Python按同一简化契约复核。']
  ];
  var ol = h('div', 'mf-steps-doc');
  steps.forEach(function (s, i) {
    var row = h('div', 'mf-step-doc');
    row.appendChild(h('div', 'mf-step-num', String(i + 1)));
    var body = h('div');
    body.appendChild(h('div', 'mf-step-title', s[0]));
    body.appendChild(h('div', 'mf-step-text', s[1]));
    row.appendChild(body);
    ol.appendChild(row);
  });
  card.appendChild(ol);
  root.appendChild(card);

  var card2 = h('div', 'mf-card');
  card2.appendChild(h('h3', null, '如何阅读因子检验'));
  var ul = h('ul', 'mf-list');
  [
    '排序预测能力（Rank IC）：信号日的因子排序与未来收益排序是否一致。+1完全同序，0接近无线性秩关联，−1完全反序。IC=0.05不是收益率5%。',
    'ICIR = IC均值 / IC标准差；阈值只用于探索排序，不能证明样本外有效，须考虑时间依赖与多次试验。',
    '方向正确期占比：预设方向修正后的Rank IC>0的期数占比；不是组合赚钱概率，也不是选券胜率。',
    '五分位先按当期可得因子分组，再计算未来收益；标签缺失率单列。重叠的20/60日收益只展示平均收益差，不伪装成可执行净值。',
    '训练段与验证段之间剔除收益标签跨界的观测；未经事前锁定的历史切分不称真正未触碰样本外。HAC与多重检验修正也不消除反复试验带来的过拟合。'
  ].forEach(function (t) { ul.appendChild(h('li', null, t)); });
  card2.appendChild(ul);
  root.appendChild(card2);

  var card3 = h('div', 'mf-card');
  card3.appendChild(h('h3', null, '浏览器与Python：同一简化研究核算契约'));
  var tb = h('table', 'mf-table');
  tb.innerHTML = '<thead><tr><th>环节</th><th>浏览器（本页）</th><th>Python（run_lab_config.py）</th></tr></thead>' +
    '<tbody>' +
    '<tr><td>收益链接</td><td>独立全市场日行情，数量/现金逐日盯市</td><td>数量/现金逐日盯市；标签另算</td></tr>' +
    '<tr><td>换手成本</td><td>实际买卖金额/NAV，含首建</td><td>同定义；正成交量与T+1收盘价代理</td></tr>' +
    '<tr><td>缺价/摘牌</td><td>锁定数量、最后观察价暂估；核验付款日、价格与依据后才释放现金</td><td>同规则；旧价回收仅限显式情景，票息税费仍缺失</td></tr>' +
    '<tr><td>控换手</td><td>向TopK目标按实际成交预算移动</td><td>同规则；不放宽、不承诺LP最优</td></tr>' +
    '<tr><td>绩效指标</td><td>逐日净值，252交易日年化；周胜率单列</td><td>同口径日波动、日回撤与日均收益夏普</td></tr>' +
    '<tr><td>范围</td><td>研究重建：分数张、现金零息、未模拟票息/赎回/容量</td><td>保存同版本实验；仍受相同数据与现金流局限</td></tr>' +
    '</tbody>';
  card3.appendChild(tb);
  root.appendChild(card3);
}

/* ------------------------------ 视图：② 因子库 ------------------------------ */
var LIB_QUERY='', LIB_FAMILY='all', LIB_ONLY_SELECTED=false, LIB_DIRS={};
function researchFields(){
  return FIELDS.concat(CFG.custom.map(function(c){return {k:c.key,n:c.name,c:'自定义',family:'自定义',d:c.desc||c.expr,formula:c.expr,unit:'由表达式决定',source:'用户表达式',limitations:['需独立时间验证'],status:'custom'};}));
}
function openFactorResearch(key,gi){
  window.MFResearchUI?.setOptions({key:key,group:gi,direction:factorDir(key,gi)});
  showView('ic');
}
function vLibrary() {
  var root=$('mf-view-library');clear(root);
  var fields=researchFields(), families=Array.from(new Set(fields.map(function(f){return f.family||f.c;}))).sort();
  var heading=h('div','mf-card');heading.appendChild(h('h3',null,'因子目录与组合配置'));
  heading.appendChild(h('p','mf-sub',FIELDS.length+' 个目录字段 · '+FIELDS.filter(function(f){return f.selectable!==false;}).length+' 个有历史观测 · '+families.length+' 个因子族（窗口变体分别列示）。字段多不等于有效因子多；先说明经济假设和方向，再选择时间区间检验。'));
  heading.appendChild(h('p','mf-sub','这里展示定义、数据来源和覆盖率。预测能力请点击“按区间检验”；不会把全样本IC当作长期有效性的结论。'));
  root.appendChild(heading);
  var bar=h('div','mf-toolbar'),gtabs=h('div','mf-tabs');
  GROUPS.forEach(function(g,gi){var b=h('button','mf-tab'+(gi===CUR_GROUP?' on':''),g+'（'+CFG.sel[gi].length+'）');b.onclick=function(){CUR_GROUP=gi;vLibrary();};gtabs.appendChild(b);});bar.appendChild(gtabs);
  var reset=h('button','mf-btn','恢复该组示例因子');reset.onclick=function(){CFG.sel[CUR_GROUP]=defaultCfg().sel[CUR_GROUP];saveCfg();vLibrary();};bar.appendChild(reset);root.appendChild(bar);
  var filters=h('div','mf-toolbar'),search=h('input','mf-input');search.type='search';search.placeholder='搜索名称、字段、公式或说明';search.setAttribute('aria-label','搜索因子目录');search.value=LIB_QUERY;filters.appendChild(search);
  var family=h('select','mf-input');family.setAttribute('aria-label','因子族');[['all','全部因子族']].concat(families.map(function(x){return [x,x];})).forEach(function(v){var op=h('option',null,v[1]);op.value=v[0];family.appendChild(op);});family.value=LIB_FAMILY;filters.appendChild(family);
  var onlyLabel=h('label','mf-ctl'),only=h('input');only.type='checkbox';only.checked=LIB_ONLY_SELECTED;onlyLabel.appendChild(only);onlyLabel.appendChild(document.createTextNode('只看已选'));filters.appendChild(onlyLabel);root.appendChild(filters);
  var count=h('p','mf-sub'),wrap=h('div','mf-table-wrap');root.appendChild(count);root.appendChild(wrap);
  var latest=WEEKS[WEEKS.length-1],latestRows=latest?latest.rows.filter(function(r){return r[1]===CUR_GROUP;}):[];
  function draw(){
    clear(wrap);var selMap={};CFG.sel[CUR_GROUP].forEach(function(x){selMap[x.k]=x.dir;});
    var rows=fields.filter(function(f){return (LIB_FAMILY==='all'||(f.family||f.c)===LIB_FAMILY)&&(!LIB_ONLY_SELECTED||selMap[f.k]!=null)&&(!LIB_QUERY||[f.n,f.k,f.d,f.formula,f.family,f.c].join(' ').toLowerCase().includes(LIB_QUERY.toLowerCase()));});
    count.textContent='显示 '+rows.length+' / '+fields.length+' 个字段；覆盖率为 '+(latest?.d||'—')+' 当前类型截面有效值占比，历史覆盖率在检验页单独计算。';
    var tb=h('table','mf-table mf-lib-table');tb.innerHTML='<thead><tr><th>入选</th><th>因子 / 字段</th><th>因子族</th><th>定义与数据口径</th><th>最新覆盖率</th><th>预设方向</th><th>研究</th></tr></thead>';var body=h('tbody');
    rows.forEach(function(f){
      var tr=h('tr',selMap[f.k]!=null?'mf-row-on':''),td=h('td'),cb=h('input');cb.type='checkbox';cb.checked=selMap[f.k]!=null;cb.disabled=f.selectable===false;cb.setAttribute('aria-label','纳入'+f.n);td.appendChild(cb);tr.appendChild(td);
      var label=h('td','mf-k',f.n);label.appendChild(h('div','mf-sub',f.k));tr.appendChild(label);tr.appendChild(h('td',null,f.family||f.c));
      var desc=h('td','mf-desc');desc.appendChild(h('div',null,f.d||''));var detail=h('details');detail.appendChild(h('summary',null,'公式、来源与限制'));detail.appendChild(h('p','mf-sub','公式：'+(f.formula||'见定义')+'；单位：'+(f.unit||'见字段说明')+'；回看窗口：'+(f.lookback||'截面')+'。'));detail.appendChild(h('p','mf-sub','来源：'+(f.source||'本地历史面板')+'；状态：'+({available:'可计算',proxy:'代理指标',custom:'自定义',unavailable:'缺少历史观测'}[f.status]||'研究代理')));detail.appendChild(h('p','mf-sub',(Array.isArray(f.limitations)?f.limitations:[f.limitations||'历史时点覆盖以数据说明为准']).join('；')));desc.appendChild(detail);tr.appendChild(desc);
      var valid=latestRows.filter(function(r){var v=rowFactor(r,f.k);return v!=null&&isFinite(v);}).length;tr.appendChild(h('td','mf-num',latestRows.length?fmtPct(valid/latestRows.length,0):'—'));
      var dirCell=h('td'),dir=h('select','mf-dir-sel');dir.disabled=f.selectable===false;dir.setAttribute('aria-label',f.n+'预设方向');[[1,'越大越优'],[-1,'越小越优']].forEach(function(x){var op=h('option',null,x[1]);op.value=x[0];dir.appendChild(op);});dir.value=String(selMap[f.k]??LIB_DIRS[CUR_GROUP+':'+f.k]??factorDir(f.k,CUR_GROUP));dirCell.appendChild(dir);if(Number(f.direction_hint)===0&&!f.dir?.[CUR_GROUP])dirCell.appendChild(h('div','mf-sub','方向待验证；当前设置不代表经济结论'));tr.appendChild(dirCell);
      cb.onchange=function(){if(cb.checked)CFG.sel[CUR_GROUP].push({k:f.k,dir:Number(dir.value)});else CFG.sel[CUR_GROUP]=CFG.sel[CUR_GROUP].filter(function(x){return x.k!==f.k;});saveCfg();tr.className=cb.checked?'mf-row-on':'';gtabs.children[CUR_GROUP].textContent=GROUPS[CUR_GROUP]+'（'+CFG.sel[CUR_GROUP].length+'）';};
      dir.onchange=function(){LIB_DIRS[CUR_GROUP+':'+f.k]=Number(dir.value);CFG.sel[CUR_GROUP].forEach(function(x){if(x.k===f.k)x.dir=Number(dir.value);});saveCfg();};
      var action=h('td'),research=h('button','mf-btn mf-btn-sm',f.selectable===false?'缺少历史观测':'按区间检验');research.disabled=f.selectable===false;research.onclick=function(){window.MFResearchUI?.setOptions({key:f.k,group:CUR_GROUP,direction:Number(dir.value)});showView('ic');};action.appendChild(research);tr.appendChild(action);body.appendChild(tr);
    });tb.appendChild(body);wrap.appendChild(tb);
  }
  search.oninput=function(){LIB_QUERY=search.value;draw();};family.onchange=function(){LIB_FAMILY=family.value;draw();};only.onchange=function(){LIB_ONLY_SELECTED=only.checked;draw();};draw();
  var pending=D.pending_catalog||[];if(pending.length){var box=h('details','mf-card');box.appendChild(h('summary',null,'待接历史数据的研究方向（'+pending.length+'项，未纳入可计算数量）'));pending.forEach(function(f){box.appendChild(h('p','mf-sub',(f.n||f.name||f.k)+'：'+(f.reason||f.d||f.description||JSON.stringify(f))));});root.appendChild(box);}
  var summary=h('div','mf-note');summary.textContent='当前类型使用 '+CFG.sel[CUR_GROUP].length+' 个因子等权打分。先在有效性检验中比较方向、区间、分层与相关性，再到组合回测评估费用与实际持仓。';root.appendChild(summary);
}

/* ------------------------------ 视图：③ 自创因子 ------------------------------ */
function vCustom() {
  var root = $('mf-view-custom');
  clear(root);
  var card = h('div', 'mf-card');
  card.appendChild(h('h3', null, '自创因子：用表达式组合现有字段'));
  card.appendChild(h('p', 'mf-sub', '表达式在每周信号日截面上逐券求值；非法值（log≤0、除0、缺失操作数）按缺失处理（打分时填0）。可引用内置字段与其他自创因子（不允许循环引用）。'));
  var syntax = h('div', 'mf-code');
  syntax.textContent = '字段：price, cb_value, bond_value, flat_prem, prem, prem_z3, ytm, dual_low, dl_z6, r_cv20, r_cb10, r_cb20, r120_z6, diff10, boll120, turn120, turn_month, turn5, cb_vol20, cv_vol20, rem_years, issue_size_yi, amount_avg3 …（完整字段见②因子目录）\n运算：+ - * / ^ ( )    函数：log(x) abs(x) sqrt(x) neg(x) min(a,b) max(a,b) pow(a,b)\n示例：r_cb20 - r_cv20（转债相对平价代理涨幅）  log(issue_size_yi)（对数规模）  r_cb10 / max(turn5, 1)（单位换手动量）';
  card.appendChild(syntax);
  root.appendChild(card);

  /* 已有自创因子列表 */
  var listCard = h('div', 'mf-card');
  listCard.appendChild(h('h3', null, '我的自创因子（' + CFG.custom.length + '个）'));
  if (!CFG.custom.length) {
    listCard.appendChild(h('p', 'mf-sub', '暂无。在下方新建，保存后自动进入②因子库（标★），可为每个类型单独勾选并指定方向。'));
  } else {
    CFG.custom.forEach(function (c, idx) {
      var row = h('div', 'mf-cf-row' + (c.__err ? ' mf-cf-err' : ''));
      var head = h('div', 'mf-cf-head');
      head.appendChild(h('span', 'mf-k', c.name + '（' + c.key + '）'));
      if (c.__err) head.appendChild(h('span', 'mf-err-badge', '表达式错误：' + c.__err));
      var btns = h('span', 'mf-cf-btns');
      var useB = h('button', 'mf-btn mf-btn-sm', '加入当前组');
      useB.onclick = function () {
        if (!c.__ast) { alert('表达式有误，请先修正'); return; }
        var exists = CFG.sel[CUR_GROUP].some(function (p) { return p.k === c.key; });
        if (!exists) { CFG.sel[CUR_GROUP].push({ k: c.key, dir: 1 }); saveCfg(); }
        window.__mfLabShowView && window.__mfLabShowView('library');
      };
      var editB = h('button', 'mf-btn mf-btn-sm', '编辑');
      editB.onclick = function () { fillEditor(c); };
      var delB = h('button', 'mf-btn mf-btn-sm mf-btn-danger', '删除');
      delB.onclick = function () {
        if (!confirm('删除自创因子「' + c.name + '」？')) return;
        for (var g = 0; g < GROUPS.length; g++) {
          CFG.sel[g] = CFG.sel[g].filter(function (p) { return p.k !== c.key; });
        }
        CFG.custom.splice(idx, 1);
        compileCustoms(); saveCfg(); vCustom();
      };
      btns.appendChild(useB); btns.appendChild(editB); btns.appendChild(delB);
      head.appendChild(btns);
      row.appendChild(head);
      row.appendChild(h('div', 'mf-cf-expr', c.expr));
      if (c.desc) row.appendChild(h('div', 'mf-sub', c.desc));
      listCard.appendChild(row);
    });
  }
  root.appendChild(listCard);

  /* 编辑器 */
  var ed = h('div', 'mf-card');
  ed.appendChild(h('h3', null, '新建 / 编辑自创因子'));
  var form = h('div', 'mf-form');
  var nameIn = h('input', 'mf-input'); nameIn.placeholder = '因子名称（如：量价背离）'; nameIn.maxLength = 24;
  var exprIn = h('textarea', 'mf-textarea'); exprIn.rows = 2; exprIn.placeholder = '表达式，如：r_cb10 / max(turn5, 1)';
  var descIn = h('input', 'mf-input'); descIn.placeholder = '备注（可选）：逻辑假设';
  var msg = h('div', 'mf-msg');
  form.appendChild(h('label', 'mf-label', '名称')); form.appendChild(nameIn);
  form.appendChild(h('label', 'mf-label', '表达式')); form.appendChild(exprIn);
  form.appendChild(h('label', 'mf-label', '备注')); form.appendChild(descIn);
  form.appendChild(msg);
  var btnRow = h('div', 'mf-btnrow');
  var testB = h('button', 'mf-btn mf-btn-primary', '试算验证');
  var saveB = h('button', 'mf-btn', '保存因子');
  btnRow.appendChild(testB); btnRow.appendChild(saveB);
  form.appendChild(btnRow);
  ed.appendChild(form);
  var preview = h('div', 'mf-preview');
  ed.appendChild(preview);
  root.appendChild(ed);

  var editingKey = null;
  function fillEditor(c) {
    editingKey = c.key; nameIn.value = c.name; exprIn.value = c.expr; descIn.value = c.desc || '';
    preview.replaceChildren(); msg.textContent = ''; msg.className = 'mf-msg';
    ed.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  }
  function tryCompile() {
    var src = exprIn.value.trim();
    if (!src) { msg.textContent = '请输入表达式'; msg.className = 'mf-msg mf-msg-err'; return null; }
    var r = parseExpr(src);
    if (r.err) {
      msg.textContent = '错误：' + r.err;
      msg.className = 'mf-msg mf-msg-err';
      return null;
    }
    return r;
  }
  testB.onclick = function () {
    var r = tryCompile();
    preview.replaceChildren();
    if (!r) return;
    /* 找最近一个有前向收益的周做试算 */
    var wk = null;
    for (var k = WEEKS.length - 2; k >= 0; k--) { if (WEEKS[k].e != null) { wk = WEEKS[k]; break; } }
    if (!wk) { msg.textContent = '无可用试算周'; return; }
    var ast = r.ast;
    var stats = { n: 0, miss: 0, min: Infinity, max: -Infinity, vals: [] };
    var samples = [];
    for (var gi = 0; gi < GROUPS.length; gi++) {
      for (var i = 0; i < wk.rows.length; i++) {
        var row = wk.rows[i];
        if (row[1] !== gi) continue;
        var v = evalAst(ast, function (key2, st) { return rowFactor(row, key2, st); });
        if (v == null) { stats.miss++; continue; }
        stats.n++; stats.min = Math.min(stats.min, v); stats.max = Math.max(stats.max, v);
        stats.vals.push(v);
        samples.push({ gi: gi, bi: row[0], v: v, fwd: row[2] });
      }
    }
    stats.vals.sort(function (a, b) { return a - b; });
    var med = stats.vals.length ? qSorted(stats.vals, 0.5) : null;
    var head = h('div', null, '试算周 ' + wk.d + '（执行日 ' + wk.e + '）：有效样本 ' + stats.n + ' · 缺失 ' + stats.miss +
      ' · 最小 ' + fmtN(stats.min, 3) + ' · 中位 ' + fmtN(med, 3) + ' · 最大 ' + fmtN(stats.max, 3));
    head.className = 'mf-ok';
    preview.appendChild(head);
    /* 该周截面IC（与下周收益） */
    var ics = [];
    for (var g2 = 0; g2 < GROUPS.length; g2++) {
      var xs = [], ys = [];
      samples.forEach(function (s) {
        if (s.gi !== g2 || s.fwd == null) return;
        xs.push(s.v); ys.push(s.fwd);
      });
      var ic = spearman(xs, ys);
      if (ic != null) ics.push(GROUPS[g2] + '：' + fmtN(ic, 4));
    }
    if (ics.length) preview.appendChild(h('div', 'mf-sub', '该周截面IC（vs 下周收益）：' + ics.join('　')));
    /* Top5 / Bottom5 */
    samples.sort(function (a, b) { return b.v - a.v; });
    var top = samples.slice(0, 5), bot = samples.slice(-5).reverse();
    var mk = function (title, arr) {
      var d = h('div', 'mf-mini');
      d.appendChild(h('div', 'mf-sub', title));
      var t = h('table', 'mf-table');
      t.innerHTML = '<thead><tr><th>转债</th><th>类型</th><th class="mf-num">因子值</th><th class="mf-num">下周收益</th></tr></thead>';
      var tb2 = h('tbody');
      arr.forEach(function (s) {
        var tr = h('tr');
        tr.innerHTML = '<td>' + esc(BONDS[s.bi][0] + ' ' + BONDS[s.bi][1]) + '</td><td>' + GROUPS[s.gi] +
          '</td><td class="mf-num">' + fmtN(s.v, 3) + '</td><td class="mf-num">' + (s.fwd == null ? '—' : fmtPctS(s.fwd)) + '</td>';
        tb2.appendChild(tr);
      });
      t.appendChild(tb2); d.appendChild(t);
      return d;
    };
    var two = h('div', 'mf-two-col');
    two.appendChild(mk('最大值前5', top));
    two.appendChild(mk('最小值前5', bot));
    preview.appendChild(two);
    msg.textContent = '表达式有效';
    msg.className = 'mf-msg mf-msg-ok';
  };
  saveB.onclick = function () {
    var r = tryCompile();
    if (!r) return;
    var name = nameIn.value.trim();
    if (!name) { msg.textContent = '请输入因子名称'; msg.className = 'mf-msg mf-msg-err'; return; }
    var expr = exprIn.value.trim();
    if (editingKey) {
      for (var i = 0; i < CFG.custom.length; i++) {
        if (CFG.custom[i].key === editingKey) {
          CFG.custom[i].name = name; CFG.custom[i].expr = expr; CFG.custom[i].desc = descIn.value.trim();
        }
      }
    } else {
      var maxN = 0;
      CFG.custom.forEach(function (c) { var m = /^cf_(\d+)$/.exec(c.key); if (m) maxN = Math.max(maxN, Number(m[1])); });
      CFG.custom.push({ key: 'cf_' + (maxN + 1), name: name, expr: expr, desc: descIn.value.trim() });
    }
    compileCustoms(); saveCfg();
    editingKey = null; nameIn.value = ''; exprIn.value = ''; descIn.value = '';
    msg.textContent = '已保存（进入②因子库可勾选使用）';
    msg.className = 'mf-msg mf-msg-ok';
    vCustom();
  };
}

/* Research continuation imports a validated copy; existing custom definitions are
 * never overwritten. All archived custom references travel together. */
function planResearchDefinitions(definitions, composition) {
  var errors=[],warnings=[],defs={},reserved=new Set(CFG.custom.map(function(c){return c.key;})),map={},additions=[];
  function collect(c){
    var key=c.key||c.k,expr=c.expr||c.formula;
    if(!/^cf_[A-Za-z0-9_]+$/.test(key||'')||typeof expr!=='string'||!expr.trim()){errors.push('自定义因子字段或公式无效：'+key);return;}
    if(defs[key]&&defs[key].expr!==expr){errors.push('档案中自定义因子定义冲突：'+key);return;}
    defs[key]={key:key,name:c.name||c.n||key,expr:expr,desc:c.desc||c.d||''};reserved.add(key);
  }
  (definitions||[]).filter(function(f){return f.status==='custom'||f.c==='自定义'||/^cf_/.test(f.k||'');}).forEach(collect);
  if(composition){
    if(composition.schema!=='StrategySpec/mf/2'||composition.method_version!=='mf-research/2.2-quality')errors.push('复合配置版本不受支持，不能按当前打分方法静默替换。');
    if(!Array.isArray(composition.custom_factors))errors.push('复合配置缺少自定义定义清单。');else composition.custom_factors.forEach(collect);
  }
  var serial=1;
  Object.keys(defs).forEach(function(k){map[k]=k;if(CFG.custom.some(function(c){return c.key===k;})){while(reserved.has('cf_'+serial))serial++;map[k]='cf_'+serial++;reserved.add(map[k]);warnings.push('复制自定义因子 '+k+' → '+map[k]+'，原定义保持不变。');}});
  var visiting={},visited={};
  function visit(k){if(visiting[k]){errors.push('自定义因子循环依赖：'+k);return;}if(visited[k])return;visiting[k]=true;var parsed=parseExpr(defs[k].expr);if(parsed.err)errors.push(k+'：'+parsed.err);else Object.keys(parsed.used||{}).forEach(function(dep){if(dep in FIDX)return;if(!defs[dep])errors.push(k+' 缺少归档依赖 '+dep+'；不会混用当前同名因子。');else visit(dep);});visiting[k]=false;visited[k]=true;}
  Object.keys(defs).forEach(visit);
  Object.keys(defs).forEach(function(k){var c=defs[k];additions.push({key:map[k],name:c.name+(map[k]!==k?'（档案副本）':''),expr:c.expr.replace(/[A-Za-z_][A-Za-z0-9_]*/g,function(token){return map[token]||token;}),desc:c.desc});});
  var selections=null,params=null;
  if(composition){
    selections=GROUPS.map(function(group){var values=composition.groups&&composition.groups[group];if(!Array.isArray(values)){errors.push('复合配置缺少类型组：'+group);return [];}var used=new Set();return values.map(function(v){var k=v.key;if(typeof k!=='string'||(!(k in FIDX)&&!defs[k]))errors.push('复合配置字段不存在或缺少归档定义：'+k);if(v.dir!==1&&v.dir!==-1)errors.push('复合配置方向无效：'+k);if(used.has(k))errors.push('复合配置重复因子：'+k);used.add(k);return {k:map[k]||k,dir:v.dir};});});
    var p=composition.params||{},period=composition.period||[];
    if(!Number.isFinite(p.top_ratio)||!(p.top_ratio>0&&p.top_ratio<=1)||!Number.isFinite(p.cost_per_side_bps)||p.cost_per_side_bps<0||p.cost_per_side_bps>10000)errors.push('复合配置选券比例或成本无效。');
    if(p.turnover_limit!=null&&(!Number.isFinite(p.turnover_limit)||p.turnover_limit<0||p.turnover_limit>2))errors.push('复合配置换手上限无效。');
    if(['combo'].concat(GROUPS).indexOf(p.mode)<0||['initial_equal','weekly_equal'].indexOf(p.allocation_mode||'initial_equal')<0)errors.push('复合配置组合模式无效。');
    var validDate=function(x){return typeof x==='string'&&/^\d{4}-\d{2}-\d{2}$/.test(x)&&Number.isFinite(Date.parse(x+'T00:00:00Z'))&&new Date(x+'T00:00:00Z').toISOString().slice(0,10)===x;};
    if(period.length!==2||!validDate(period[0])||!validDate(period[1])||period[0]<D.period[0]||period[1]>D.period[1]||period[0]>period[1])errors.push('复合组合回测区间超出当前数据范围。');
    params={topRatio:p.top_ratio,turnover:p.turnover_limit!=null,turnoverLimit:p.turnover_limit==null?0.5:p.turnover_limit,costBps:p.cost_per_side_bps,mode:p.mode==='combo'?'combo':String(GROUPS.indexOf(p.mode)),allocationMode:p.allocation_mode||'initial_equal',start:period[0],end:period[1]};
    warnings.push('复合档案将带入三类因子选择、方向及组合参数；当前配置另存本地恢复副本，旧研究结果不修改。');
  }
  return {errors:Array.from(new Set(errors)),warnings:warnings,keyMap:map,additions:additions,selections:selections,params:params};
}
function applyResearchDefinitions(definitions,composition){
  var plan=planResearchDefinitions(definitions,composition);if(plan.errors.length)throw Error(plan.errors.join('；'));
  // Complete validation precedes all mutations. Keep the previous strategy for
  // recovery before applying an explicitly requested composite replacement.
  if(composition){try{localStorage.setItem('mf_lab_config_before_research_import',JSON.stringify(cfgToJson()));}catch(e){throw Error('无法保存当前组合的恢复副本，配置尚未修改。请先导出当前配置。');}}
  CFG.custom=CFG.custom.concat(plan.additions);if(plan.selections)CFG.sel=plan.selections;if(plan.params)CFG.params=Object.assign({},CFG.params,plan.params);
  compileCustoms();if(plan.additions.length||composition)saveCfg();return {keyMap:plan.keyMap};
}
window.openFactorResearchDraft=function(value){
  var frozen=JSON.parse(JSON.stringify(value));
  // Stage before navigation so the first load does not launch default research.
  if(!window.MFResearchUI)throw Error('因子研究界面尚未加载，请刷新页面。');
  window.MFResearchUI.stageDraft(frozen);window.showTab?.('mf-lab');ensureData(function(){showView('ic');});
};

/* ------------------------------ 视图：④ IC验证 ------------------------------ */
function vIC() {
  var root=$('mf-view-ic');
  if(!window.MFResearchUI||!window.MFResearch){clear(root);root.appendChild(h('p','mf-note','因子研究模块未加载，请检查分享包是否包含 mf_research_engine.js 和 mf_research_ui.js。'));return;}
  window.MFResearchUI.render(root,{
    data:D,valueGetter:function(row,key){return rowFactor(row,key);},scoreGetter:scoreGroup,
    getComposition:function(){return cfgToJson();},
    getFields:researchFields,getSelectedKeys:function(group){var groups=group==='all'?[0,1,2]:[Number(group)];return Array.from(new Set(groups.flatMap(function(g){return (CFG.sel[g]||[]).map(function(x){return x.k;});})));},
    getDirection:factorDir,inspectResearchDefinitions:planResearchDefinitions,applyResearchDefinitions:applyResearchDefinitions,
    onOptionsChange:function(opts){},
    onUseFactor:function(key,dir,group){
      if(key==='__score')return;
      var groups=group==='all'?[0,1,2]:[Number(group)];groups.forEach(function(g){var old=CFG.sel[g].find(function(x){return x.k===key;});if(old)old.dir=dir;else CFG.sel[g].push({k:key,dir:dir});});
      var opts=window.MFResearchUI.getOptions();CFG.params.start=opts.start;CFG.params.end=opts.end;saveCfg();
    }
  });
}

/* ------------------------------ 视图：⑤ 组合回测 ------------------------------ */
function vBacktest() {
  var root = $('mf-view-bt');
  clear(root);
  root.appendChild(h('h3',null,'组合回测：将研究假设转为实际模拟持仓'));
  root.appendChild(h('p','mf-sub','因子检验衡量排序关系；组合回测另外计算现金、费用、换手与持仓。中性化选项仅作用于诊断，不会自动改变这里的等权标准分策略。'));
  var bar = h('div', 'mf-toolbar');
  var dateInputs={};['start','end'].forEach(function(key){var label=h('label','mf-ctl',key==='start'?'回测开始日':'回测结束日'),input=h('input','mf-input');input.type='date';input.min=D.period[0];input.max=D.period[1];input.value=CFG.params[key]||D.period[key==='start'?0:1];input.setAttribute('aria-label',key==='start'?'回测开始日':'回测结束日');input.onchange=function(){CFG.params[key]=input.value;saveCfg();};label.appendChild(input);bar.appendChild(label);dateInputs[key]=input;});
  var usePeriod=h('button','mf-btn','采用当前因子检验区间');usePeriod.onclick=function(){var opts=window.MFResearchUI?.getOptions?.();if(!opts)return;CFG.params.start=opts.start;CFG.params.end=opts.end;saveCfg();vBacktest();};bar.appendChild(usePeriod);
  function mkSel(label, opts, val, onchange) {
    var wrap2 = h('label', 'mf-ctl');
    wrap2.appendChild(h('span', null, label));
    var s = h('select', 'mf-input');
    opts.forEach(function (o) { var op = h('option', null, o[1]); op.value = String(o[0]); s.appendChild(op); });
    s.value = String(val);
    s.onchange = function () { onchange(s.value); saveCfg(); };
    wrap2.appendChild(s);
    return wrap2;
  }
  bar.appendChild(mkSel('多头比例', [[0.10, '前10%'], [0.15, '前15%'], [0.20, '前20%（默认）'], [0.25, '前25%'], [0.30, '前30%'], [0.50, '前50%']], CFG.params.topRatio, function (v) { CFG.params.topRatio = Number(v); }));
  bar.appendChild(mkSel('组合范围', [['combo', '三类组合（配置分配方式）'], [0, '仅偏债型'], [1, '仅平衡型'], [2, '仅偏股型']], CFG.params.mode, function (v) { CFG.params.mode = (v === 'combo') ? 'combo' : Number(v); }));
  bar.appendChild(mkSel('类间资金', [['initial_equal','期初各1/3，之后漂移'],['weekly_equal','每周目标各1/3（计调仓成本）']], CFG.params.allocationMode || 'initial_equal', function(v) { CFG.params.allocationMode=v; }));
  var tcWrap = h('label', 'mf-ctl');
  var tcCb = h('input'); tcCb.type = 'checkbox'; tcCb.checked = CFG.params.turnover;
  var tcSel = h('select', 'mf-input');
  [[0.3, '≤30%'], [0.5, '≤50%'], [0.7, '≤70%']].forEach(function (o) { var op = h('option', null, o[1]); op.value = String(o[0]); tcSel.appendChild(op); });
  tcSel.value = String(CFG.params.turnoverLimit);
  tcCb.onchange = function () { CFG.params.turnover = tcCb.checked; saveCfg(); };
  tcSel.onchange = function () { CFG.params.turnoverLimit = Number(tcSel.value); saveCfg(); };
  tcWrap.appendChild(tcCb);
  tcWrap.appendChild(h('span', null, '双边成交预算（含首建）'));
  tcWrap.appendChild(tcSel);
  bar.appendChild(tcWrap);
  bar.appendChild(mkSel('成本(bp/边)', [[0, '0'], [5, '5（默认）'], [10, '10'], [15, '15'], [20, '20']], CFG.params.costBps, function (v) { CFG.params.costBps = Number(v); }));
  var runB = h('button', 'mf-btn mf-btn-primary', '运行回测');
  bar.appendChild(runB);
  root.appendChild(bar);

  var out = h('div', 'mf-bt-out');
  bar.addEventListener('change', function(){LAST_BT=null;clear(out);out.appendChild(h('p','mf-sub','参数已修改，请重新运行以生成新实验结果。'));});
  root.appendChild(out);

  function kpiCard(label, value, sub, cls) {
    var c = h('div', 'mf-kpi' + (cls ? ' ' + cls : ''));
    c.appendChild(h('div', 'mf-kpi-l', label));
    c.appendChild(h('div', 'mf-kpi-v', value));
    if (sub) c.appendChild(h('div', 'mf-kpi-s', sub));
    return c;
  }
  function perfTable(title, m, idxM, valuation) {
    var card = h('div', 'mf-card');
    card.appendChild(h('h3', null, title));
    var tb = h('table', 'mf-table');
    var rows = [
      ['回测总收益率', fmtPctS(m.total), fmtPctS(idxM.total)],
      ['年化收益率', fmtPctS(m.ann), fmtPctS(idxM.ann)],
      ['年化超额收益', fmtPctS(mfSafeExcess(m.ann, idxM.ann)), '—'],
      ['年化波动率', fmtPct(m.vol), fmtPct(idxM.vol)],
      ['最大回撤', fmtPct(m.mdd), fmtPct(idxM.mdd)],
      ['夏普比率', fmtN(m.sharpe), fmtN(idxM.sharpe)],
      ['卡玛比率', fmtN(m.calmar), fmtN(idxM.calmar)],
      ['周度胜率', fmtPct(m.winRate), fmtPct(idxM.winRate)],
      ['盈亏比', fmtN(m.pl), fmtN(idxM.pl)],
      ['调仓周数', String(m.weeks || '—'), String(idxM.weeks || '—')]
      ,['期末未核实估值 / NAV', fmtPct(valuation.end_share), '—']
      ,['最高未核实估值 / NAV', fmtPct(valuation.max_share), '—']
    ];
    tb.innerHTML = '<thead><tr><th>指标</th><th class="mf-num">本组合</th><th class="mf-num">中证转债指数</th></tr></thead><tbody>' +
      rows.map(function (r) { return '<tr><td>' + r[0] + '</td><td class="mf-num">' + r[1] + '</td><td class="mf-num">' + r[2] + '</td></tr>'; }).join('') +
      '</tbody>';
    card.appendChild(tb);
    return card;
  }
  function drawResult() {
    clear(out);
    var bt = LAST_BT;
    if (!bt) return;
    /* KPI */
    var m = bt.metrics, im = bt.idxMetrics;
    var ex = mfSafeExcess(m.ann, im.ann, bt.benchmark_quality);
    var kpis = h('div', 'mf-kpis');
    kpis.appendChild(kpiCard('年化收益', fmtPctS(m.ann), '指数 ' + fmtPctS(im.ann)));
    kpis.appendChild(kpiCard('年化超额', fmtPctS(ex), null, ex >= 0 ? 'mf-kpi-good' : 'mf-kpi-bad'));
    kpis.appendChild(kpiCard('最大回撤', fmtPct(m.mdd), null, m.mdd > -0.1 ? 'mf-kpi-good' : ''));
    kpis.appendChild(kpiCard('夏普比率', fmtN(m.sharpe), null, (m.sharpe || 0) >= 1 ? 'mf-kpi-good' : ''));
    kpis.appendChild(kpiCard('周度胜率', fmtPct(m.winRate), '盈亏比 ' + fmtN(m.pl)));
    var avgTO = mean(bt.turnovers);
    kpis.appendChild(kpiCard('周均换手(双边)', fmtPct(avgTO), '耗时' + bt.ms + 'ms'));
    kpis.appendChild(kpiCard('期末未核实估值占比',fmtPct(bt.unresolved_summary.end_share),'区间最高 '+fmtPct(bt.unresolved_summary.max_share)));
    out.appendChild(kpis);

    /* 净值曲线 */
    var series = [
      { label: '本组合（期末 ' + fmtN(bt.combo[bt.combo.length - 1], 3) + '）', color: PALETTE[0], values: bt.combo, width: 2.4 },
      { label: '中证转债指数（期末 ' + fmtN(bt.idx[bt.idx.length - 1], 3) + '）', color: PALETTE[1], values: bt.idx, width: 1.8 }
    ];
    if (REF.mf_combo && CFG.params.mode === 'combo' && Array.isArray(REF.mf_combo.dates) && JSON.stringify(REF.mf_combo.dates)===JSON.stringify(bt.dates)) {
      series.push({ label: '同版本报告默认组合', color: PALETTE[3], values: REF.mf_combo.nav.slice(0, bt.combo.length), width: 1.6 });
    }
    var chartCard = h('div', 'mf-card');
    chartCard.innerHTML = svgLine('组合净值对比（周度，成本' + CFG.params.costBps + 'bp/边' + (CFG.params.turnover ? '，控换手≤' + Math.round(CFG.params.turnoverLimit * 100) + '%' : '') + '）', series, { dates: bt.dates });
    out.appendChild(chartCard);

    /* 绩效表 */
    out.appendChild(h('p','mf-sub','实际模拟区间：'+bt.dates[0]+' 至 '+bt.dates.at(-1)+'；信号沿数据集固定5交易日节奏，区间开头以现金起步。'));
    out.appendChild(perfTable('所选区间绩效（vs 中证转债指数）', m, im, bt.unresolved_summary));
    var bq=bt.benchmark_quality;
    var quality=h('div','mf-note','研究重建 · '+bt.metadata.method_version+' · 数据 '+bt.metadata.data_version.slice(0,12)+' · 类间分配 '+bt.metadata.allocation_mode+'。未计票息、税费与容量；摘牌缺付款证据不释放现金，'+Object.keys(bt.unresolvedSettlements||{}).length+'项未核实回收。结算模式 '+((D.market||{}).settlementMode||'evidence_only')+'；评级含公告调整、初始反推与最新代理，非严格PIT认证。缺价持仓保留数量并暂估，共'+bt.issues.length+'项持仓缺价记录。未核实估值占NAV：期末 '+fmtPct(bt.unresolved_summary.end_share)+'，区间最高 '+fmtPct(bt.unresolved_summary.max_share)+'。基准有效 '+bq.observed_points+'/'+bq.expected_points+' 点（'+fmtPct(bq.coverage)+'），有效观测 '+(bq.first_valid_date||'无')+' 至 '+(bq.last_valid_date||'无')+'；'+(bq.complete?'使用完整观测计算。':'首尾/中间缺价不补值，基准及超额派生指标留空。')+'金额以初始资金=1归一，模型数量不是实际张数或账户元；档案中0%/50%/100%回收率为期末账面估值敏感性，现金不变，不是真实兑付或结算。');
    out.appendChild(quality);
    var save=h('button','mf-btn mf-btn-primary','保存研究结果');
    save.onclick=async function(){
      save.disabled=true;save.textContent='正在保存…';
      try{
        if(typeof window.saveResearchRun==='function'){
          var receipt=await window.saveResearchRun(multifactorRunSnapshot(bt));
          if(receipt&&receipt.saved_to==='browser')save.textContent='已保存到浏览器研究库';
          else if(receipt&&receipt.saved_to==='download')save.textContent='已下载结果JSON（未存入研究库）';
          else throw Error('未收到有效的保存回执');
        }else{archive.click();save.textContent='研究库不可用，已下载结果JSON';}
      }catch(e){save.textContent='保存失败，可下载JSON';quality.textContent='保存失败：'+e.message;}
      finally{save.disabled=false;}
    };out.appendChild(save);
    var archive=h('button','mf-btn','下载本次冻结结果JSON');
    archive.onclick=function(){var b=new Blob([JSON.stringify(multifactorRunSnapshot(bt))],{type:'application/json'}),a=document.createElement('a');a.href=URL.createObjectURL(b);a.download='mf_run_'+bt.metadata.data_version.slice(0,12)+'_'+Date.now()+'.json';a.click();setTimeout(function(){URL.revokeObjectURL(a.href);},1000);};out.appendChild(archive);


    /* 分年度 */
    var yCard = h('div', 'mf-card');
    yCard.appendChild(h('h3', null, '分年度表现'));
    var ytb = h('table', 'mf-table');
    ytb.innerHTML = '<thead><tr><th>年份</th><th class="mf-num">组合收益</th><th class="mf-num">指数收益</th><th class="mf-num">超额</th><th class="mf-num">最大回撤</th><th class="mf-num">周胜率</th><th class="mf-num">周数</th></tr></thead>';
    var yb = h('tbody');
    var yr = null;
    try { yr = yearlyTable(bt); } catch (e) { }
    if (yr) {
      yr.forEach(function (r) {
        var tr = h('tr');
        tr.innerHTML = '<td>' + r.year + '</td><td class="mf-num">' + fmtPctS(r.ret) + '</td><td class="mf-num">' + fmtPctS(r.idx) +
          '</td><td class="mf-num">' + fmtPctS(r.excess) + '</td><td class="mf-num">' + fmtPct(r.mdd) + '</td><td class="mf-num">' +
          fmtPct(r.winRate, 0) + '</td><td class="mf-num">' + r.weeks + '</td>';
        yb.appendChild(tr);
      });
    }
    ytb.appendChild(yb);
    yCard.appendChild(ytb);
    out.appendChild(yCard);

    /* 与官方对照说明 */
    if (REF.mf_combo && CFG.params.mode === 'combo' && Array.isArray(REF.mf_combo.dates) && JSON.stringify(REF.mf_combo.dates)===JSON.stringify(bt.dates)) {
      var refN = REF.mf_combo.nav, myN = bt.combo;
      var n = Math.min(refN.length, myN.length);
      var diffs = [];
      for (var i = 1; i < n; i++) diffs.push(myN[i] / myN[i - 1] - refN[i] / refN[i - 1]);
      var te = stdev(diffs) * Math.sqrt(CONSTS.weeksPerYear);
      var note = h('div', 'mf-note');
      note.appendChild(h('div', null, '与同版本报告默认组合对照：期末本组合 ' + fmtN(myN[n - 1], 3) + ' vs 对照 ' + fmtN(refN[n - 1], 3) +
        '，跟踪误差(年化) ' + fmtPct(te) + '。'));
      note.appendChild(h('div', 'mf-sub', '仅比较同方法、同数据版本与同分配方式的结果；旧绩效不能沿用为新版本结果。两端均为不含完整现金流的研究重建。'));
      out.appendChild(note);
    }

    /* 最新信号持仓（下周执行名单） */
    var lastCard = h('div', 'mf-card');
    lastCard.appendChild(h('h3', null, '最新信号持仓（' + (WEEKS[WEEKS.length - 1].d) + ' 信号 · 未约束TopK信号预览；非实际目标仓位）'));
    var hasAny = false;
    var lt = h('table', 'mf-table');
    lt.innerHTML = '<thead><tr><th>类型</th><th>转债</th><th class="mf-num">权重</th><th class="mf-num">复合得分</th></tr></thead>';
    var lb = h('tbody');
    var lastWeek = WEEKS[WEEKS.length - 1];
    modeGroupsOf().forEach(function (gi) {
      var sc = scoreGroup(lastWeek, gi);
      if (!sc) return;
      var K = Math.max(1, Math.ceil(sc.rows.length * CFG.params.topRatio));
      var order = [];
      for (var i = 0; i < sc.rows.length; i++) order.push({ i: i, s: sc.scores[i] });
      order.sort(function (a, b) { return b.s - a.s; });
      order.slice(0, K).forEach(function (o) {
        hasAny = true;
        var tr = h('tr');
        tr.innerHTML = '<td>' + GROUPS[gi] + '</td><td>' + esc(BONDS[sc.rows[o.i][0]][0] + ' ' + BONDS[sc.rows[o.i][0]][1]) +
          '</td><td class="mf-num">' + fmtN(1 / K, 2) + '%</td><td class="mf-num">' + fmtN(o.s, 3) + '</td>';
        lb.appendChild(tr);
      });
    });
    if (hasAny) { lt.appendChild(lb); lastCard.appendChild(lt); }
    else lastCard.appendChild(h('p', 'mf-sub', '当前配置在最新信号日无有效持仓（检查因子选择与表达式）。'));
    out.appendChild(lastCard);

    /* 历史调仓浏览器 */
    var histCard = h('div', 'mf-card');
    histCard.appendChild(h('h3', null, '历史调仓明细'));
    var hctl = h('div', 'mf-toolbar');
    var hsel = h('select', 'mf-input');
    var recs = [];
    for (var s2 = 0; s2 < bt.accounts.length; s2++) {
      var sl = bt.accounts[s2];
      for (var w2 = 0; w2 < sl.holdings.length; w2++) {
        if (sl.holdings[w2]) recs.push({ s: s2, w: w2, hold: sl.holdings[w2] });
      }
    }
    recs.forEach(function (r, i) {
      var op = h('option', null, (r.hold.group < 0 ? '三类实际组合' : GROUPS[r.hold.group]) + ' · ' + r.hold.d + '（信号日）');
      op.value = String(i);
      hsel.appendChild(op);
    });
    hsel.value = String(Math.max(0, recs.length - 1));
    hctl.appendChild(hsel);
    var dlB = h('button', 'mf-btn', '导出当前回测全部调仓（CSV）');
    dlB.onclick = exportHoldingsCsv;
    hctl.appendChild(dlB);
    histCard.appendChild(hctl);
    var htable = h('div');
    histCard.appendChild(htable);
    function drawHold() {
      clear(htable);
      var r = recs[Number(hsel.value)];
      if (!r) return;
      var t = h('table', 'mf-table');
      t.innerHTML = '<thead><tr><th>转债</th><th class="mf-num">权重</th><th class="mf-num">复合得分</th></tr></thead>';
      var b = h('tbody');
      r.hold.list.forEach(function (x) {
        var tr = h('tr');
        tr.innerHTML = '<td>' + esc(BONDS[x.bi][0] + ' ' + BONDS[x.bi][1]) + '</td><td class="mf-num">' + fmtN(x.w * 100, 2) + '%</td><td class="mf-num">' + fmtN(x.score, 3) + '</td>';
        b.appendChild(tr);
      });
      t.appendChild(b);
      htable.appendChild(t);
      htable.appendChild(h('p', 'mf-sub', '信号日 ' + r.hold.d + ' · 执行日 ' + r.hold.e + ' · ' + r.hold.list.length + ' 只实际模拟持仓'));
    }
    hsel.onchange = drawHold;
    drawHold();
    out.appendChild(histCard);
  }
  function modeGroupsOf() {
    return CFG.params.mode === 'combo' ? [0, 1, 2] : [Number(CFG.params.mode)];
  }
  runB.onclick = function () {
    runB.disabled = true; runB.textContent = '计算中…';
    setTimeout(function () {
      try { runBacktest(); drawResult(); }
      catch (e) { out.replaceChildren(); out.appendChild(h('div', 'mf-err-badge', '回测失败：' + e.message)); }
      runB.disabled = false; runB.textContent = '运行回测';
    }, 30);
  };
  if (LAST_BT) drawResult();
  else out.appendChild(h('p', 'mf-sub', '按所选时间区间及②③配置运行，每5交易日出信号。非交易日起点从首个可用信号开始；期末按区间最后交易日计价，包含成本与换手统计。'));
}
function exportHoldingsCsv() {
  if (!LAST_BT) return;
  var lines = ['sleeve_group,signal_date,exec_date,code,name,weight,composite_score'];
  LAST_BT.accounts.forEach(function (sl) {
    sl.holdings.forEach(function (hd) {
      if (!hd) return;
      hd.list.forEach(function (x) {
        lines.push([hd.group < 0 ? "三类实际组合" : GROUPS[hd.group], hd.d, hd.e, BONDS[x.bi][0], BONDS[x.bi][1],
        x.w.toFixed(6), x.score == null ? "" : x.score.toFixed(4)].join(','));
      });
    });
  });
  var blob = new Blob(['\ufeff' + lines.join('\n')], { type: 'text/csv;charset=utf-8' });
  var a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = 'mf_lab_holdings_' + new Date().toISOString().slice(0, 10).replace(/-/g, '') + '.csv';
  a.click();
  URL.revokeObjectURL(a.href);
}

/* ------------------------------ 视图：⑥ 导出复核 ------------------------------ */
function vExport() {
  var root = $('mf-view-export');
  clear(root);
  var card = h('div', 'mf-card');
  card.appendChild(h('h3', null, '导出冻结配置 → Python研究复核'));
  card.appendChild(h('p', 'mf-sub', '导出StrategySpec及数据哈希；run_lab_config.py核对输入版本并生成独立实验目录，保存数量账本、未成交、费用与数据局限。数据是研究重建，Python运行不自动提升为严格历史时点回测。'));
  root.appendChild(card);

  /* 配置摘要 */
  var sum = h('div', 'mf-card');
  sum.appendChild(h('h3', null, '当前配置摘要'));
  var ul = h('ul', 'mf-list');
  GROUPS.forEach(function (g, gi) {
    var names = CFG.sel[gi].map(function (p) { return fieldName(p.k) + (p.dir < 0 ? '↓' : '↑'); });
    ul.appendChild(h('li', null, g + '（' + names.length + '个）：' + (names.join('、') || '（空）')));
  });
  if (CFG.custom.length) {
    ul.appendChild(h('li', null, '自创因子：' + CFG.custom.map(function (c) { return c.name + ' = ' + c.expr; }).join('；')));
  } else ul.appendChild(h('li', null, '自创因子：无'));
  ul.appendChild(h('li', null, '参数：多头前' + Math.round(CFG.params.topRatio * 100) + '% · ' +
    (CFG.params.mode === 'combo' ? '三类合成' : '仅' + GROUPS[Number(CFG.params.mode)]) + ' · ' +
    (CFG.params.turnover ? '控换手≤' + Math.round(CFG.params.turnoverLimit * 100) + '%' : '不控换手') + ' · 成本' + CFG.params.costBps + 'bp/边'));
  sum.appendChild(ul);
  root.appendChild(sum);

  /* JSON */
  var jc = h('div', 'mf-card');
  jc.appendChild(h('h3', null, '配置文件 mf_lab_config.json'));
  var ta = h('textarea', 'mf-textarea mf-code-ta');
  ta.rows = 14; ta.readOnly = true;
  ta.value = JSON.stringify(cfgToJson(), null, 2);
  jc.appendChild(ta);
  var br = h('div', 'mf-btnrow');
  var cp = h('button', 'mf-btn', '复制配置');
  cp.onclick = function () {
    ta.select();
    try { document.execCommand('copy'); cp.textContent = '已复制'; setTimeout(function () { cp.textContent = '复制配置'; }, 1500); }
    catch (e) { }
  };
  var dl = h('button', 'mf-btn mf-btn-primary', '下载 mf_lab_config.json');
  dl.onclick = function () {
    var blob = new Blob([JSON.stringify(cfgToJson(), null, 2)], { type: 'application/json' });
    var a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'mf_lab_config.json';
    a.click();
    URL.revokeObjectURL(a.href);
  };
  br.appendChild(cp); br.appendChild(dl);
  try{var previous=localStorage.getItem('mf_lab_config_before_research_import');if(previous){var recovery=h('button','mf-btn','下载带入前组合配置');recovery.onclick=function(){var blob=new Blob([previous],{type:'application/json'}),url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download='mf_lab_before_research_import.json';a.click();setTimeout(function(){URL.revokeObjectURL(url);},1000);};br.appendChild(recovery);}}catch(e){}
  jc.appendChild(br);
  root.appendChild(jc);

  /* 运行指令 */
  var rc = h('div', 'mf-card');
  rc.appendChild(h('h3', null, '复核步骤'));
  var code = h('div', 'mf-code');
  code.textContent = '# 1) 将 mf_lab_config.json 保存到项目根目录（与 cb_multifactor_backtest.py 同级）\n' +
    '# 2) 运行研究复核（日频数量账本 · 严格双边预算 · 缺价锁仓 · 独立实验档案）\n' +
    'python3 run_lab_config.py --config mf_lab_config.json\n\n' +
    '# 输出目录：backtest_results/mf_lab/<配置名>/\n' +
    '#   nav_curve.csv / nav_vs_index.png   净值曲线（vs 中证转债指数 000832）\n' +
    '#   performance_summary.csv            全区间 + 分年度绩效（总收益/年化/回撤/夏普/胜率/盈亏比/波动）\n' +
    '#   rebalance_holdings.csv             每次调仓持仓名单与权重\n' +
    '#   run_meta.json                      本次配置与口径存档';
  rc.appendChild(code);
  rc.appendChild(h('p', 'mf-sub', '两端使用同一版本化简化契约；须按逐日数量、现金、费用和未成交核对，不能仅比较最终收益。Python运行不改变历史评级、现金流和容量缺口。'));
  root.appendChild(rc);
}

/* ------------------------------ 视图路由 ------------------------------ */
var VIEWS = [
  ['ic', '① 有效性检验'],
  ['library', '② 因子目录与配置'],
  ['custom', '③ 自定义因子'],
  ['method', '④ 研究方法'],
  ['bt', '⑤ 组合回测'],
  ['export', '⑥ 导出复核']
];
function showView(name) {
  VIEW = name;
  VIEWS.forEach(function (v) {
    var sec = $('mf-view-' + v[0]);
    if (sec) sec.style.display = (v[0] === name) ? '' : 'none';
    var btn = document.querySelector('#mf-steps [data-v="' + v[0] + '"]');
    if (btn) btn.className = 'mf-step-btn' + (v[0] === name ? ' on' : '');
  });
  switch (name) {
    case 'method': vMethod(); break;
    case 'library': vLibrary(); break;
    case 'custom': vCustom(); break;
    case 'ic': vIC(); break;
    case 'bt': vBacktest(); break;
    case 'export': vExport(); break;
  }
}
window.__mfLabShowView = showView;

/* ------------------------------ 数据加载与初始化 ------------------------------ */
function validateLabPackedHeader(value, schema) {
  if(!value||value.schema!==schema||value.codec!=='gzip-base64-json')throw Error('不支持的多因子压缩数据格式');
  if(!Number.isInteger(value.uncompressed_bytes)||value.uncompressed_bytes<=0||typeof value.sha256!=='string'||!/^[a-f0-9]{64}$/.test(value.sha256))throw Error('多因子载荷缺少有效的长度或SHA-256校验信息');
  if(schema==='mf-parts/1'&&(!Number.isInteger(value.total)||value.total<1||value.total>64||!Array.isArray(value.parts)))throw Error('多因子分片清单无效（分片数须为1至64的整数）');
}
async function decodeLabPackedChunksCore(chunks, header) {
  if(typeof DecompressionStream!=='function')throw Error('当前浏览器不支持DecompressionStream；请使用近期Chrome、Edge或Safari，不能改用旧核算数据');
  if(!globalThis.crypto||!globalThis.crypto.subtle)throw Error('当前页面无法校验SHA-256；请使用HTTPS或127.0.0.1本地服务打开，不会跳过完整性校验');
  // Validate every slot before releasing encoded strings. A sparse array whose
  // length equals total is still missing data, not a complete manifest.
  for(var i=0;i<chunks.length;i++){
    if(typeof chunks[i]!=='string'||!chunks[i].length||chunks[i].length%4!==0||!(/^[A-Za-z0-9+/]*={0,2}$/).test(chunks[i])||(i<chunks.length-1&&chunks[i].indexOf('=')>=0))throw Error('多因子第'+(i+1)+'片缺失或Base64格式错误');
  }
  var arrays=new Array(chunks.length);
  for(var j=0;j<chunks.length;j++){
    var binary=atob(chunks[j]);chunks[j]=null;var bytes=new Uint8Array(binary.length);
    for(var k=0;k<binary.length;k++)bytes[k]=binary.charCodeAt(k);
    arrays[j]=bytes;binary=null;
  }
  // Blob accepts multiple binary chunks directly: avoid concatenating another
  // full compressed copy before decoding the >200MB research payload.
  var archive=new Blob(arrays);arrays=null;
  var raw=await new Response(archive.stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();archive=null;
  if(raw.byteLength!==header.uncompressed_bytes)throw Error('多因子数据长度校验失败；分片可能不完整或版本混合，请重试');
  var digest=await globalThis.crypto.subtle.digest('SHA-256',raw);
  var hex=Array.from(new Uint8Array(digest)).map(function(b){return b.toString(16).padStart(2,'0');}).join('');
  if(hex!==header.sha256)throw Error('多因子SHA-256校验失败；分片版本不一致或内容损坏，请等待生成完成后重试');
  return JSON.parse(new TextDecoder().decode(raw));
}
function labPackedWorkerMain(){
  self.onmessage=async function(event){
    try{var data=await decodeLabPackedChunksCore(event.data.chunks,event.data.header);self.postMessage({ok:true,data:data});}
    catch(error){self.postMessage({ok:false,error:error.message||String(error)});}
  };
}
async function decodeLabPackedChunks(chunks,header){
  // A Blob worker also works in the offline share package. It uses precisely
  // the same decoder and SHA checks; unsupported worker environments retain
  // the checked decoder, never an unchecked or older payload.
  var worker=null,url=null;
  if(typeof Worker==='function'&&typeof URL!=='undefined'&&typeof URL.createObjectURL==='function'){
    try{url=URL.createObjectURL(new Blob([decodeLabPackedChunksCore.toString(),'\n(',labPackedWorkerMain.toString(),')();'],{type:'text/javascript'}));worker=new Worker(url);}
    catch(_){if(url)URL.revokeObjectURL(url);url=null;}
  }
  if(!worker)return decodeLabPackedChunksCore(chunks,header);
  try{
    var data=await new Promise(function(resolve,reject){
      var timeout=setTimeout(function(){reject(Error('多因子后台解码超时；请检查浏览器内存后重试'));},180000);
      worker.onmessage=function(event){clearTimeout(timeout);if(event.data.ok)resolve(event.data.data);else reject(Error(event.data.error||'多因子后台解码失败'));};
      worker.onerror=function(event){clearTimeout(timeout);reject(Error('多因子后台解码失败：'+(event.message||'Worker不可用')));};
      try{worker.postMessage({chunks:chunks,header:{uncompressed_bytes:header.uncompressed_bytes,sha256:header.sha256}});}catch(error){clearTimeout(timeout);reject(error);}
    });
    chunks.fill(null);return data;
  }finally{worker.terminate();URL.revokeObjectURL(url);}
}
async function unpackLabData(packed) {
  validateLabPackedHeader(packed,'mf-packed/1');
  return decodeLabPackedChunks([packed.data],packed);
}
async function unpackLabDataParts(parts) {
  validateLabPackedHeader(parts,'mf-parts/1');
  if(parts.parts.length!==parts.total)throw Error('多因子分片数量不完整');
  return decodeLabPackedChunks(parts.parts,parts);
}
function multifactorRunSnapshot(bt) {
  if (!bt) return null;
  var usedBonds={},weekKeys=['d','e','signal_at','execution_at','holding_start','holding_end'];
  // Weeks reference the complete input cross-sections in the live engine.
  // Strip those inputs before JSON serialization visits them; retain every
  // account result and ledger so existing result viewers keep their paths.
  var snapshot=JSON.parse(JSON.stringify({schema_version:'research-run/1',kind:'multifactor',
    name:'分类型多因子 · '+bt.metadata.allocation_mode+' · '+bt.dates[0]+'至'+bt.dates[bt.dates.length-1],
    config:bt.strategy,metadata:bt.metadata,result:bt},function(key,value){
      if(key==='weeks'&&Array.isArray(value))return value.map(function(w){
        var interval={};weekKeys.forEach(function(k){if(w[k]!=null)interval[k]=w[k];});return interval;
      });
      if(value&&typeof value==='object'){
        if(Number.isInteger(value.bi)&&value.bi>=0)usedBonds[value.bi]=true;
        if(key==='finalUnits'||key==='target'||key==='budgeted_target'){
          Object.keys(value).forEach(function(bi){if(/^\d+$/.test(bi))usedBonds[bi]=true;});
        }
      }
      return value;
    }));
  snapshot.result.bond_lookup={};
  Object.keys(usedBonds).forEach(function(bi){
    var bond=BONDS&&BONDS[Number(bi)];
    snapshot.result.bond_lookup[bi]={code:bond?bond[0]:null,name:bond?bond[1]:null};
  });
  snapshot.result.archive_contract={version:'mf-result/2',weeks:'date/execution intervals only; input cross-sections excluded',
    bond_lookup:'keys are the bi identifiers used by holdings, orders, targets and finalUnits'};
  return snapshot;
}
window.getMultifactorResearchRunSnapshot=function(){return multifactorRunSnapshot(LAST_BT);};
function loadLabScript(src, onload, onerror) {
  var s = document.createElement('script');
  s.src = src; s.onload = onload; s.onerror = onerror;
  document.head.appendChild(s);
}
var labTransportWarning='';
function ensureData(cb) {
  if(dataLoaded){cb();return;}
  dataWaiters.push(cb);if(dataLoading)return;dataLoading=true;
  var msg=$('mf-load-msg'),failed=false;
  if(msg)msg.textContent='正在加载多因子数据集（分片传输，首次加载较大，请稍候）…';
  // A retry must begin with a fresh manifest, not a sparse or decoded previous
  // attempt. Parts are loaded sequentially so no old request can finish late
  // and write into the next attempt's global array.
  delete window.MF_LAB_DATA_PARTS;delete window.MF_LAB_DATA_PACKED;delete window.MF_LAB_DATA;
  labTransportWarning='';
  function fail(reason){
    if(failed)return;failed=true;dataLoading=false;booted=false;dataWaiters=[];
    delete window.MF_LAB_DATA_PARTS;delete window.MF_LAB_DATA_PACKED;delete window.MF_LAB_DATA;
    var root=$('mf-root'),loading=$('mf-load');if(root)root.style.display='none';if(loading)loading.style.display='';
    if(msg)msg.textContent=reason+'。请确认完整文件已生成并随站点发布；重新进入多因子页签可重试。';
  }
  async function finish(){
    if(failed)return;
    try{
      if(window.MF_LAB_DATA_PARTS){window.MF_LAB_DATA=await unpackLabDataParts(window.MF_LAB_DATA_PARTS);delete window.MF_LAB_DATA_PARTS;}
      else if(window.MF_LAB_DATA_PACKED){window.MF_LAB_DATA=await unpackLabData(window.MF_LAB_DATA_PACKED);delete window.MF_LAB_DATA_PACKED;}
      else if(window.MF_LAB_DATA){labTransportWarning='兼容旧版未压缩载荷：未提供整体SHA-256校验';}
      else throw Error('多因子数据缺失');
      init();dataLoading=false;
      var waiters=dataWaiters.splice(0);waiters.forEach(function(fn){try{fn();}catch(e){console.error(e);}});
    }catch(e){fail('初始化失败：'+e.message);console.error(e);}
  }
  loadLabScript('multifactor_lab_data.p1.js',function(){
    var parts=window.MF_LAB_DATA_PARTS;
    try{validateLabPackedHeader(parts,'mf-parts/1');if(parts.parts.length!==1||typeof parts.parts[0]!=='string')throw Error('首片必须携带完整清单及第1片数据');}
    catch(e){fail(e.message);return;}
    function next(n){
      if(failed)return;
      if(n>parts.total)return finish();
      if(msg)msg.textContent='正在加载多因子数据分片 '+n+' / '+parts.total+'…';
      var name='multifactor_lab_data.p'+n+'.js';
      loadLabScript(name+'?v='+parts.sha256,function(){
        if(failed)return;
        if(window.MF_LAB_DATA_PARTS!==parts||typeof parts.parts[n-1]!=='string'){fail('数据文件 '+name+' 未提供预期分片');return;}
        return next(n+1);
      },function(){fail('数据文件 '+name+' 加载失败');});
    }
    return next(2);
  },function(){
    // First-part 404 is the only legacy fallback; an incomplete modern set must
    // not silently display a different old dataset after a later part fails.
    delete window.MF_LAB_DATA_PARTS;
    loadLabScript('multifactor_lab_data.js',finish,function(){fail('数据文件 multifactor_lab_data.p1.js / multifactor_lab_data.js 加载失败');});
  });
}
function init() {
  D = window.MF_LAB_DATA;
  if (!D) throw new Error('MF_LAB_DATA 缺失');
  if (![2,3].includes(D.v) || !D.market || !D.metadata) throw new Error('多因子数据格式不兼容，请重新生成研究版载荷');
  FIELDS = D.fields;
  FIDX = {};
  FIELDS.forEach(function (f, i) { FIDX[f.k] = i; });
  BONDS = D.bonds; WEEKS = D.weeks; GROUPS = D.groups;
  CONSTS = D.consts; REF = D.ref || {}; IDXNAV = D.idxNav;
  ICMETA = D.icMeta || {}; DEFAULTS = D.defaults || {};
  loadCfg();
  /* 元信息 */
  var meta = $('mf-meta');
  if (meta) {
    clear(meta);
    meta.appendChild(h('span', 'mf-badge', '数据生成 ' + D.generated));
    meta.appendChild(h('span', 'mf-badge', '核算区间 ' + D.period[0] + ' ~ ' + D.period[1]));
    meta.appendChild(h('span', 'mf-badge', WEEKS.length + ' 周截面'));
    meta.appendChild(h('span', 'mf-badge', BONDS.length + ' 只转债'));
    meta.appendChild(h('span', 'mf-badge', FIELDS.length + ' 个可计算字段'));
    if(labTransportWarning)meta.appendChild(h('span','mf-badge',labTransportWarning));
    var reset = h('button', 'mf-btn mf-btn-sm', '重置全部配置');
    reset.onclick = function () {
      if (!confirm('清空自创因子并恢复报告默认因子配置？')) return;
      resetCfg(); showView(VIEW);
    };
    meta.appendChild(reset);
  }
  var loadEl = $('mf-load'), rootEl = $('mf-root');
  if (loadEl) loadEl.style.display = 'none';
  if (rootEl) rootEl.style.display = '';
  /* 步骤导航 */
  var steps = $('mf-steps');
  if (steps) {
    clear(steps);
    VIEWS.forEach(function (v) {
      var b = h('button', 'mf-step-btn' + (v[0] === VIEW ? ' on' : ''), v[1]);
      b.setAttribute('data-v', v[0]);
      b.onclick = function () { showView(v[0]); };
      steps.appendChild(b);
    });
  }
  dataLoaded = true;
  showView(VIEW);
}
window.__mfLabTest = {
  configure: function(data, config) {
    D=data; FIELDS=data.fields; FIDX={}; FIELDS.forEach(function(f,i){FIDX[f.k]=i;});
    BONDS=data.bonds; WEEKS=data.weeks; GROUPS=data.groups; CONSTS=data.consts;
    DEFAULTS=data.defaults||{}; REF={}; IDXNAV=data.idxNav||[]; CFG=config||defaultCfg();
    compileCustoms();
  }, runSleeve:runSleeve, runBacktest:runBacktest, boundedTarget:boundedTarget,
  scoreGroup:scoreGroup, config:cfgToJson, planResearchDefinitions:planResearchDefinitions, applyResearchDefinitions:applyResearchDefinitions, unpack:unpackLabData, unpackParts:unpackLabDataParts, snapshot:multifactorRunSnapshot
};
window.__mfLabOnShown = function () {
  if (booted) return;
  booted = true;
  ensureData(function () { });
};
})();
