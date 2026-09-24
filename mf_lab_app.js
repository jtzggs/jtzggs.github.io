/* ============================================================================
 * 多因子实验室 · 浏览器端应用逻辑
 * 数据：multifactor_lab_data.js（window.MF_LAB_DATA，懒加载）
 * 口径：与 cb_multifactor_backtest.py（研报分类型多因子框架本地实现）一致
 *   - 三分类（平底溢价率：<-20% 偏债 / ±20% 平衡 / >20% 偏股）
 *   - 组内 MAD去极值(±3×1.4826×MAD) → 截面ZSCORE → 缺失填0
 *   - 复合得分 = mean(dir × z)，前 topRatio 等权多头
 *   - 信号日收盘 → T+1收盘成交，双边成本；浏览器版为周度速算近似，
 *     Python 精确复核见 run_lab_config.py（日频引擎 + LP控换手 + 摘牌退出）
 * ============================================================================ */
(function () {
'use strict';

/* ------------------------------ 全局状态 ------------------------------ */
var D = null;                 // window.MF_LAB_DATA
var FIELDS = null, FIDX = {}, BONDS = null, WEEKS = null, GROUPS = null;
var CONSTS = null, REF = null, IDXNAV = null, ICMETA = null, DEFAULTS = null;
var CFG = null;               // 用户配置
var LAST_BT = null;           // 最近一次回测结果
var VIEW = 'method';          // 当前子视图
var CUR_GROUP = 0;            // 因子库当前组
var IC_GROUP = 0;             // IC验证当前组
var dataLoaded = false, dataLoading = false, booted = false;
var exprCache = {};

var LS_KEY = 'mf_lab_cfg_v1';
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
        if (args.length < 1 || args.length > 2) return { err: tok.v + ' 参数个数错误' };
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
  return 1;
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
    params: { topRatio: CONSTS.topRatio, turnover: false, turnoverLimit: 0.5, costBps: 5, mode: 'combo' }
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
      CFG.params = o.params;
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
    version: 1,
    name: 'mf_lab_' + new Date().toISOString().slice(0, 10).replace(/-/g, ''),
    source: 'mf_lab_browser',
    created_at: new Date().toISOString(),
    period: D.period,
    custom_factors: CFG.custom.map(function (c) {
      return { key: c.key, name: c.name, expr: c.expr, desc: c.desc || '' };
    }),
    groups: groups,
    params: {
      top_ratio: CFG.params.topRatio,
      turnover_limit: CFG.params.turnover ? CFG.params.turnoverLimit : null,
      cost_per_side_bps: CFG.params.costBps,
      mode: CFG.params.mode
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
function selectTopKC(sc, K, prevSet, limit) {
  /* 控换手启发式（Python 版为 LP 精确解）：
     至少保留 ceil(K×(1-limit)) 只旧券（按本周得分排序取优），其余按得分补齐 */
  var order = [];
  for (var i = 0; i < sc.rows.length; i++) order.push({ i: i, s: sc.scores[i] });
  order.sort(function (a, b) { return b.s - a.s; });
  var rank = {};
  for (var r = 0; r < order.length; r++) rank[order[r].i] = r;
  var minKeep = Math.ceil(K * (1 - limit));
  var prevList = [];
  for (var j = 0; j < sc.rows.length; j++) {
    if (prevSet && prevSet[sc.rows[j][0]]) prevList.push({ i: j, s: sc.scores[j] });
  }
  prevList.sort(function (a, b) { return b.s - a.s; });
  var chosen = {}, keep = Math.min(minKeep, K, prevList.length);
  for (var p = 0; p < keep; p++) chosen[prevList[p].i] = 1;
  for (var q = 0; q < order.length && Object.keys(chosen).length < K; q++) chosen[order[q].i] = 1;
  return chosen;
}
/* 单类型 sleeve 回测：返回 {nav[], rets[], turnovers[], holdings[k], weeks[k]} */
function runSleeve(gi) {
  var sel = CFG.sel[gi];
  var nav = 1, navs = [1], rets = [], turnovers = [];
  var prevW = {};  // bondIdx → weight（上周目标权重）
  var holdings = [], usedWeeks = [];
  var costRate = CFG.params.costBps / 1e4;
  for (var k = 0; k < WEEKS.length; k++) {
    var w = WEEKS[k];
    if (w.e == null) break;  // 最后一周仅预览
    var sc = scoreGroup(w, gi);
    var target = {};  // bondIdx → weight
    var holdRec = null;
    if (sc && sel.length) {
      var K = Math.max(1, Math.ceil(sc.rows.length * CFG.params.topRatio));
      var chosen;
      if (CFG.params.turnover) {
        var prevSet = {};
        for (var c in prevW) prevSet[c] = 1;
        chosen = selectTopKC(sc, K, prevSet, CFG.params.turnoverLimit);
      } else {
        chosen = {};
        var order = [];
        for (var i = 0; i < sc.rows.length; i++) order.push({ i: i, s: sc.scores[i] });
        order.sort(function (a, b) { return b.s - a.s; });
        for (var q = 0; q < K && q < order.length; q++) chosen[order[q].i] = 1;
      }
      var nSel = Object.keys(chosen).length;
      if (nSel > 0) {
        for (var key2 in chosen) target[sc.rows[key2][0]] = 1 / nSel;
        holdRec = { week: k, d: w.d, e: w.e, group: gi, list: [] };
        for (var key3 in chosen) {
          holdRec.list.push({
            bi: sc.rows[key3][0], w: 1 / nSel, score: sc.scores[key3]
          });
        }
        holdRec.list.sort(function (a, b) { return b.score - a.score; });
      }
    }
    /* 本周收益：对上周权重按前向收益盯市 */
    var rGross = 0, wSum = 0;
    for (var bi in prevW) {
      var fwd = null;
      if (sc) {
        for (var t = 0; t < sc.rows.length; t++) {
          if (sc.rows[t][0] === Number(bi) && sc.rows[t][2] != null) { fwd = sc.rows[t][2]; break; }
        }
      }
      if (fwd == null) fwd = 0;  // 摘牌/缺价：按最后价退出近似
      rGross += prevW[bi] * fwd;
      wSum += prevW[bi];
    }
    if (wSum > 0) rGross /= wSum;  // 有效持仓归一（权重漂移由重置处理）
    /* 换手与成本：目标权重 vs 盯市权重 */
    var cur = {};
    for (var bi2 in prevW) {
      var fwd2 = null;
      if (sc) {
        for (var t2 = 0; t2 < sc.rows.length; t2++) {
          if (sc.rows[t2][0] === Number(bi2) && sc.rows[t2][2] != null) { fwd2 = sc.rows[t2][2]; break; }
        }
      }
      if (fwd2 == null) fwd2 = 0;
      cur[bi2] = prevW[bi2] * (1 + fwd2) / (1 + rGross);
    }
    var traded = 0;
    var unionSet = {};
    for (var a in target) unionSet[a] = 1;
    for (var b in cur) unionSet[b] = 1;
    for (var u in unionSet) {
      traded += Math.abs((target[u] || 0) - (cur[u] || 0));
    }
    nav = nav * (1 + rGross) * (1 - traded * costRate);
    rets.push(rGross - traded * costRate / (1 + rGross));
    turnovers.push(traded / 2);
    navs.push(nav);
    holdings.push(holdRec);
    usedWeeks.push(w);
    prevW = target;
  }
  return { navs: navs, rets: rets, turnovers: turnovers, holdings: holdings, weeks: usedWeeks };
}
/* 组合回测（三类合成=各sleeve等权1/3，或单类型） */
function runBacktest() {
  var t0 = Date.now();
  var sleeves = [];
  var modeGroups = [];
  if (CFG.params.mode === 'combo') {
    for (var g = 0; g < GROUPS.length; g++) modeGroups.push(g);
  } else {
    modeGroups.push(Number(CFG.params.mode));
  }
  for (var i = 0; i < modeGroups.length; i++) {
    sleeves.push(runSleeve(modeGroups[i]));
  }
  /* 合成组合：三类各1/3、每周再平衡（与 Python 引擎口径一致）——
     周收益=各 sleeve 周收益均值，净值由周收益逐周复利（而非三条净值曲线平均，
     后者相当于组间不再平衡，长期会系统性偏离官方合成组合）。 */
  var n = sleeves[0].navs.length;
  var combo = [1], comboRets = [], comboTO = [];
  for (var k = 1; k < n; k++) {
    var r = 0, to = 0;
    for (var j = 0; j < sleeves.length; j++) { r += sleeves[j].rets[k - 1]; to += sleeves[j].turnovers[k - 1]; }
    r /= sleeves.length; to /= sleeves.length;
    comboRets.push(r); comboTO.push(to);
    combo.push(combo[combo.length - 1] * (1 + r));
  }
  /* 对齐指数与参照：取前 n 个点 */
  var idx = IDXNAV.slice(0, n);
  var dates = [];
  for (var d = 0; d < n; d++) {
    var wk = WEEKS[Math.min(d, WEEKS.length - 1)];
    dates.push(wk && wk.e ? wk.e : (wk ? wk.d : ''));
  }
  LAST_BT = {
    combo: combo, rets: comboRets, turnovers: comboTO, dates: dates, idx: idx,
    sleeves: sleeves, modeGroups: modeGroups, ms: Date.now() - t0,
    metrics: computeMetrics(combo, comboRets),
    idxMetrics: computeMetrics(idx, idx.map(function (v, i) { return i ? v / idx[i - 1] - 1 : 0; }).slice(1))
  };
  return LAST_BT;
}
function computeMetrics(nav, rets) {
  if (!nav || nav.length < 2) return {};
  var total = nav[nav.length - 1] / nav[0] - 1;
  var years = (nav.length - 1) / CONSTS.weeksPerYear;
  var ann = Math.pow(1 + total, 1 / Math.max(years, 1e-9)) - 1;
  var vol = stdev(rets) * Math.sqrt(CONSTS.weeksPerYear);
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
  var sharpe = vol > 0 ? (ann - CONSTS.rf) / vol : null;
  return {
    total: total, ann: ann, vol: vol, mdd: mdd, sharpe: sharpe,
    winRate: rets.length ? wins / rets.length : null,
    pl: (losses && sumL) ? (sumW / wins) / (-sumL / losses) : null,
    calmar: mdd < 0 ? ann / -mdd : null,
    weeks: rets.length
  };
}
function yearlyTable(bt) {
  var rows = {};
  var order = [];
  for (var k = 0; k < bt.rets.length; k++) {
    var wk = bt.weeks ? bt.weeks[k] : null;
    var ds = bt.dates[k + 1] || (wk ? wk.d : '');
    var y = ds ? ds.slice(0, 4) : '?';
    if (!rows[y]) { rows[y] = { rets: [], nav0: bt.combo[k], navEnd: bt.combo[k + 1], idx0: bt.idx[k], idxEnd: bt.idx[k + 1] }; order.push(y); }
    rows[y].rets.push(bt.rets[k]);
    rows[y].navEnd = bt.combo[k + 1];
    rows[y].idxEnd = bt.idx[k + 1];
  }
  var out = [];
  for (var i = 0; i < order.length; i++) {
    var y = order[i], r = rows[y];
    var yr = r.navEnd / r.nav0 - 1, yi = r.idxEnd / r.idx0 - 1;
    var m = computeMetrics([r.nav0, r.navEnd], r.rets);
    out.push({
      year: y, ret: yr, idx: yi, excess: yr - yi, mdd: m.mdd,
      winRate: m.winRate, weeks: r.rets.length
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
    ['第2步 · 样本池过滤', '剔除：上市≤2周、余额<2亿且近1月换手>100%、主体评级低于A、已公告强赎、连续无成交。数据集中每周截面已按此口径预过滤。'],
    ['第3步 · 选因子', '从32个字段（价格/估值/动量/量能/期限规模）中为每个类型挑选因子并指定方向（+1 值越大越好 / −1 越小越好）。可在「② 因子库」按 IC 统计挑选，也可在「③ 自创因子」用表达式构造新因子。'],
    ['第4步 · 数据处理', '组内截面：MAD去极值（中位数 ± 3×1.4826×MAD）→ ZSCORE标准化 → 缺失填0（等价于组内中位数替代）。'],
    ['第5步 · 打分与选券', '复合得分 = 所选因子（方向×Z）的等权平均；每类取得分前 ' + Math.round(CONSTS.topRatio * 100) + '% 构建多头组，组内等权。可选控换手（换手预算内优先保留旧持仓）。'],
    ['第6步 · 回测与复核', '信号日收盘出信号 → T+1 收盘成交，双边成本 ' + (CFG.params.costBps) + 'bp/边。浏览器内为周度速算（执行日→执行日收益直接链接），可在「⑥ 导出」生成配置交给 Python 精确复核（日频引擎 + LP控换手 + 摘牌退出处理）。']
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
  card2.appendChild(h('h3', null, 'IC 验证方法（第④步的判读标准）'));
  var ul = h('ul', 'mf-list');
  [
    '周度 IC = Spearman(因子值, 下周收益)：秩相关，对极值稳健；样本<10 的周不计。',
    'ICIR = IC均值 / IC标准差：衡量预测稳定性；|ICIR| ≥ 0.3 且 |IC均值| ≥ 0.03 通常视为有效。',
    'IC 胜率 = IC > 0 的周占比：方向稳定性的直观指标。',
    '分层检验：按因子值分5层，各层等权持有；若多头层（按方向）持续跑赢空头层，因子有效且近似单调。',
    '复合得分 IC：验证所选因子组合的整体预测力，是「因子是否选对了」的最终判据。'
  ].forEach(function (t) { ul.appendChild(h('li', null, t)); });
  card2.appendChild(ul);
  root.appendChild(card2);

  var card3 = h('div', 'mf-card');
  card3.appendChild(h('h3', null, '浏览器速算版 与 Python 精确版'));
  var tb = h('table', 'mf-table');
  tb.innerHTML = '<thead><tr><th>环节</th><th>浏览器（本页）</th><th>Python（run_lab_config.py）</th></tr></thead>' +
    '<tbody>' +
    '<tr><td>收益链接</td><td>周度（执行日→执行日前向收益，预计算）</td><td>日频盯市账本（units/cash 逐日结算）</td></tr>' +
    '<tr><td>换手成本</td><td>权重漂移近似估算</td><td>成交金额精确计费（T+1 实际成交价）</td></tr>' +
    '<tr><td>摘牌处理</td><td>缺失周按最后价近似退出</td><td>最后可得收盘价退出 + 连续缺价强平</td></tr>' +
    '<tr><td>控换手</td><td>保留优先启发式</td><td>线性规划精确解（max Σscore·w，换手≤上限）</td></tr>' +
    '<tr><td>用途</td><td>快速探索、因子筛选、参数试算</td><td>出具正式回测档案（净值图/分年度/调仓名单）</td></tr>' +
    '</tbody>';
  card3.appendChild(tb);
  root.appendChild(card3);
}

/* ------------------------------ 视图：② 因子库 ------------------------------ */
function vLibrary() {
  var root = $('mf-view-library');
  clear(root);
  /* 组别切换 */
  var bar = h('div', 'mf-toolbar');
  var gtabs = h('div', 'mf-tabs');
  GROUPS.forEach(function (g, gi) {
    var b = h('button', 'mf-tab' + (gi === CUR_GROUP ? ' on' : ''), g + '（' + CFG.sel[gi].length + '个因子）');
    b.onclick = function () { CUR_GROUP = gi; vLibrary(); };
    gtabs.appendChild(b);
  });
  bar.appendChild(gtabs);
  var resetB = h('button', 'mf-btn', '恢复报告默认因子');
  resetB.onclick = function () {
    var d = defaultCfg();
    CFG.sel[CUR_GROUP] = d.sel[CUR_GROUP];
    saveCfg(); vLibrary();
  };
  bar.appendChild(resetB);
  root.appendChild(bar);

  /* 说明 */
  root.appendChild(h('p', 'mf-sub', '勾选纳入该类型打分；方向 +1 表示因子值越大越好，−1 越小越好。IC 统计为全样本期周度值（执行日→执行日口径），颜色越深越显著，红=正、蓝=负。点击行末「📊 档案」查看该因子的详细解释与可视化（IC时序、累计IC、五分位分层、最新截面分布、分年度IC）。'));
  if (LIB_DOC && LIB_DOC.gi !== CUR_GROUP) LIB_DOC = null;

  /* 表格 */
  var wrap = h('div', 'mf-table-wrap');
  var tb = h('table', 'mf-table mf-lib-table');
  var thead = h('thead');
  thead.innerHTML = '<tr><th style="width:44px">入选</th><th>字段</th><th>类别</th><th>说明</th>' +
    '<th class="mf-num">IC均值</th><th class="mf-num">ICIR</th><th class="mf-num">IC胜率</th>' +
    '<th style="width:110px">方向</th><th class="mf-num">其他组IC</th><th style="width:70px">档案</th></tr>';
  tb.appendChild(thead);
  var tbody = h('tbody');
  var meta = {};
  var glist = ICMETA[GROUPS[CUR_GROUP]] || [];
  glist.forEach(function (r) { meta[r.k] = r; });
  var rows = FIELDS.map(function (f, i) { return { f: f, i: i, custom: false }; });
  CFG.custom.forEach(function (c) {
    rows.push({ f: { k: c.key, n: c.name, c: '自创因子', d: c.desc || c.expr, dir: {} }, i: -1, custom: true });
  });
  var selMap = {};
  CFG.sel[CUR_GROUP].forEach(function (p) { selMap[p.k] = p.dir; });
  rows.forEach(function (r) {
    var f = r.f;
    var tr = h('tr', selMap[f.k] != null ? 'mf-row-on' : null);
    var td0 = h('td');
    var cb = h('input'); cb.type = 'checkbox'; cb.checked = selMap[f.k] != null;
    cb.onchange = function () {
      if (cb.checked) {
        var dir = f.dir && f.dir[GROUPS[CUR_GROUP]] != null ? f.dir[GROUPS[CUR_GROUP]] : 1;
        CFG.sel[CUR_GROUP].push({ k: f.k, dir: dir });
      } else {
        CFG.sel[CUR_GROUP] = CFG.sel[CUR_GROUP].filter(function (p) { return p.k !== f.k; });
      }
      saveCfg();
      var tabs = document.querySelectorAll('#mf-view-library .mf-tab');
      if (tabs[CUR_GROUP]) tabs[CUR_GROUP].textContent = GROUPS[CUR_GROUP] + '（' + CFG.sel[CUR_GROUP].length + '个因子）';
      tr.className = selMap[f.k] != null ? 'mf-row-on' : '';
    };
    td0.appendChild(cb);
    tr.appendChild(td0);
    tr.appendChild(h('td', 'mf-k', f.n + (r.custom ? ' ★' : '')));
    tr.appendChild(h('td', null, r.custom ? '自创' : f.c));
    tr.appendChild(h('td', 'mf-desc', f.d));
    var st = meta[f.k];
    var tdIC = h('td', 'mf-num');
    if (st) {
      tdIC.textContent = fmtN(st.mean, 4);
      tdIC.style.background = icColor(st.mean);
      tdIC.style.color = Math.abs(st.mean) > 0.05 ? '#fff' : '#222';
    } else tdIC.textContent = '—';
    tr.appendChild(tdIC);
    var tdIR = h('td', 'mf-num');
    tdIR.textContent = st && st.icir != null ? fmtN(st.icir, 2) : '—';
    tr.appendChild(tdIR);
    var tdP = h('td', 'mf-num');
    tdP.textContent = st ? fmtPct(st.pos, 0) : '—';
    tr.appendChild(tdP);
    var tdD = h('td');
    var sel1 = h('select', 'mf-dir-sel');
    [['1', '+1 越大越好'], ['-1', '−1 越小越好']].forEach(function (o) {
      var op = h('option', null, o[1]); op.value = o[0]; sel1.appendChild(op);
    });
    sel1.value = String(selMap[f.k] != null ? selMap[f.k] : (f.dir && f.dir[GROUPS[CUR_GROUP]] != null ? f.dir[GROUPS[CUR_GROUP]] : 1));
    sel1.onchange = function () {
      var found = false;
      CFG.sel[CUR_GROUP] = CFG.sel[CUR_GROUP].map(function (p) {
        if (p.k === f.k) { found = true; return { k: f.k, dir: Number(sel1.value) }; }
        return p;
      });
      if (!found) CFG.sel[CUR_GROUP].push({ k: f.k, dir: Number(sel1.value) });
      saveCfg();
    };
    tdD.appendChild(sel1);
    tr.appendChild(tdD);
    var other = [];
    GROUPS.forEach(function (g2, gi2) {
      if (gi2 === CUR_GROUP) return;
      var m2 = (ICMETA[g2] || []).filter(function (x) { return x.k === f.k; })[0];
      if (m2) other.push(g2.slice(0, 1) + ':' + (m2.mean >= 0 ? '+' : '') + fmtN(m2.mean, 3));
    });
    tr.appendChild(h('td', 'mf-num mf-sub', other.join('  ') || '—'));
    var tdDoc = h('td');
    var docB = h('button', 'mf-btn mf-btn-sm' + (LIB_DOC && LIB_DOC.key === f.k ? ' mf-btn-primary' : ''), '📊 档案');
    docB.onclick = function (ev) {
      ev.stopPropagation();
      if (LIB_DOC && LIB_DOC.key === f.k && LIB_DOC.gi === CUR_GROUP) {
        LIB_DOC = null;
      } else {
        LIB_DOC = { gi: CUR_GROUP, key: f.k, dir: factorDir(f.k, CUR_GROUP) };
      }
      vLibrary();
      if (LIB_DOC) {
        var el = $('mf-lib-doc');
        if (el) el.scrollIntoView({ behavior: 'smooth', block: 'start' });
      }
    };
    tdDoc.appendChild(docB);
    tr.appendChild(tdDoc);
    tbody.appendChild(tr);
  });
  tb.appendChild(tbody);
  wrap.appendChild(tb);
  root.appendChild(wrap);

  /* 因子档案面板（图表 + 详细解释） */
  var docHolder = h('div');
  docHolder.id = 'mf-lib-doc';
  root.appendChild(docHolder);
  renderFactorDoc(false);

  /* 当前配置摘要 */
  var sum = h('div', 'mf-note');
  var names = CFG.sel[CUR_GROUP].map(function (p) { return fieldName(p.k) + (p.dir < 0 ? '↓' : '↑'); });
  sum.appendChild(h('div', null, GROUPS[CUR_GROUP] + ' 当前打分因子（' + names.length + '个）：' + (names.join('、') || '（空）')));
  sum.appendChild(h('div', 'mf-sub', '↓=方向−1（值越小越好）↑=方向+1；完整流程：选好三类因子 → ③ 自创因子（可选）→ ④ IC验证 → ⑤ 组合回测。'));
  root.appendChild(sum);
}

/* ------------------------------ 因子档案（详细解释 + 可视化图表） ------------------------------ */
var LIB_DOC = null;   // {gi, key, dir, _dated, _qa, _hist}

function renderFactorDoc(scrollTo) {
  var holder = $('mf-lib-doc');
  if (!holder) return;
  clear(holder);
  if (!LIB_DOC || !WEEKS) return;
  var gi = LIB_DOC.gi, key = LIB_DOC.key, dir = LIB_DOC.dir;
  var isCustom = !(key in FIDX);
  var f = isCustom ? null : FIELDS[FIDX[key]];
  var cd = isCustom ? customDef(key) : null;
  var doc = isCustom ? null : (FACTOR_DOCS[key] || null);
  var name = fieldName(key);

  /* 计算结果缓存（方向切换时复用，避免重算） */
  if (!LIB_DOC._dated) LIB_DOC._dated = icSeriesDated(gi, key);
  if (!LIB_DOC._qa) LIB_DOC._qa = quintileAnalysis(gi, key);
  if (!LIB_DOC._hist) LIB_DOC._hist = latestGroupValues(gi, key);
  var dated = LIB_DOC._dated, qa = LIB_DOC._qa, hist = LIB_DOC._hist;
  var st = dated.ics.length ? icStats(dated.ics) : null;

  var card = h('div', 'mf-card');
  card.style.borderColor = 'var(--mfl-accent)';
  card.style.borderWidth = '1.5px';

  /* --- 标题栏 --- */
  var head = h('div', 'mf-doc-head');
  head.appendChild(h('span', 'mf-doc-title', '因子档案：' + name + '（' + key + '）'));
  head.appendChild(h('span', 'mf-badge', GROUPS[gi] + '组'));
  if (f) head.appendChild(h('span', 'mf-badge', f.c));
  if (isCustom) head.appendChild(h('span', 'mf-badge', '自创因子 ★'));
  if (f && f.dir && f.dir[GROUPS[gi]] != null) {
    head.appendChild(h('span', 'mf-badge', '报告默认方向 ' + (f.dir[GROUPS[gi]] > 0 ? '+1' : '−1')));
  }
  var dirSel = h('select', 'mf-input');
  [['1', '方向 +1（值越大越好）'], ['-1', '方向 −1（值越小越好）']].forEach(function (o) {
    var op = h('option', null, o[1]); op.value = o[0]; dirSel.appendChild(op);
  });
  dirSel.value = String(dir);
  dirSel.onchange = function () { LIB_DOC.dir = Number(dirSel.value); renderFactorDoc(false); };
  var dirLbl = h('span', 'mf-label', '图表判读方向：');
  var dirWrap = h('span', 'mf-ctl');
  dirWrap.appendChild(dirLbl); dirWrap.appendChild(dirSel);
  head.appendChild(dirWrap);
  var closeB = h('button', 'mf-btn mf-btn-sm', '收起档案 ✕');
  closeB.onclick = function () { LIB_DOC = null; vLibrary(); };
  head.appendChild(closeB);
  card.appendChild(head);
  card.appendChild(h('p', 'mf-sub', '下列 IC / 分层 / 分布均按「' + GROUPS[gi] + '」组内样本计算（周度截面，执行日→执行日口径）。图表与统计已按所选方向修正：方向修正后 IC 为正且分层多头跑赢，说明该方向下因子有效。'));

  /* --- 详细解释 --- */
  card.appendChild(h('div', 'mf-doc-sec', '一、因子定义与解释'));
  if (doc) {
    var two = h('div', 'mf-two-col');
    var c1 = h('div');
    c1.appendChild(h('div', 'mf-doc-k', '计算口径'));
    c1.appendChild(h('div', 'mf-doc-p', doc.lg));
    c1.appendChild(h('div', 'mf-doc-k', '字段说明'));
    c1.appendChild(h('div', 'mf-doc-p', f ? f.d : ''));
    var c2 = h('div');
    c2.appendChild(h('div', 'mf-doc-k', '为什么可能有效'));
    c2.appendChild(h('div', 'mf-doc-p', doc.wh));
    c2.appendChild(h('div', 'mf-doc-k', '怎么用（方向惯例）'));
    c2.appendChild(h('div', 'mf-doc-p', doc.use));
    two.appendChild(c1); two.appendChild(c2);
    card.appendChild(two);
    var risk = h('div', 'mf-doc-risk');
    risk.appendChild(h('span', 'mf-doc-k', '风险与失效场景：'));
    risk.appendChild(document.createTextNode(doc.rk));
    card.appendChild(risk);
  } else if (cd) {
    card.appendChild(h('div', 'mf-doc-p', '自创因子：' + (cd.desc || '无描述')));
    var code = h('div', 'mf-code');
    code.textContent = cd.key + ' = ' + cd.expr;
    card.appendChild(code);
    card.appendChild(h('div', 'mf-doc-p', '按表达式在每周信号日截面上逐券求值（可引用内置字段与其他自创因子）。上方方向仅用于图表判读；纳入打分请在②列表中勾选并设置方向。'));
  } else {
    card.appendChild(h('div', 'mf-doc-p', f ? f.d : ''));
  }

  /* --- KPI --- */
  if (st) {
    var adjMean = dir * st.mean, adjIcir = st.icir != null ? dir * st.icir : null;
    var adjPos = dir > 0 ? st.pos : 1 - st.pos;
    var kpis = h('div', 'mf-kpis');
    function kpi(label, val, sub, good) {
      var k = h('div', 'mf-kpi' + (good === true ? ' mf-kpi-good' : good === false ? ' mf-kpi-bad' : ''));
      k.appendChild(h('div', 'mf-kpi-l', label));
      k.appendChild(h('div', 'mf-kpi-v', val));
      if (sub) k.appendChild(h('div', 'mf-kpi-s', sub));
      kpis.appendChild(k);
    }
    var aMean = Math.abs(adjMean), aIcir = Math.abs(adjIcir || 0);
    var verdict = (aMean >= 0.03 && aIcir >= 0.3) ? '有效' : (aMean >= 0.015 ? '弱有效' : '无效');
    kpi('IC均值（方向修正）', fmtN(adjMean, 4), '原始 ' + fmtN(st.mean, 4), aMean >= 0.03);
    kpi('ICIR', adjIcir != null ? fmtN(adjIcir, 2) : '—', '稳定性', aIcir >= 0.3);
    kpi('IC胜率', fmtPct(adjPos, 0), '方向修正后', adjPos >= 0.5);
    kpi('t值', st.t != null ? fmtN(Math.abs(st.t), 2) : '—', '|t|≥2 显著', Math.abs(st.t || 0) >= 2);
    kpi('有效周数', String(st.n), '样本<10的周不计');
    kpi('判读', verdict, '全样本期', verdict === '有效');
    if (qa) {
      var longQ = dir > 0 ? 0 : 4, shortQ = dir > 0 ? 4 : 0;
      var longAnn = qa.anns[longQ], shortAnn = qa.anns[shortQ];
      var spreadAnn = Math.pow(qa.navs[0] / qa.navs[4], CONSTS.weeksPerYear / qa.weeks) - 1;
      var dirSpread = dir > 0 ? spreadAnn : -spreadAnn;
      kpi('多头层年化', fmtPctS(longAnn, 1), dir > 0 ? 'Q1（因子最高20%）' : 'Q5（因子最低20%）', longAnn > 0);
      kpi('空头层年化', fmtPctS(shortAnn, 1), dir > 0 ? 'Q5' : 'Q1', shortAnn < 0);
      kpi('多空年化', fmtPctS(dirSpread, 1), '多头−空头', dirSpread > 0);
      var desc = 0;
      for (var q = 0; q < 4; q++) if (qa.anns[q] > qa.anns[q + 1]) desc++;
      var monoTxt = dir > 0
        ? (desc >= 4 ? '强单调（Q1>Q2>…>Q5）' : desc >= 3 ? '较单调' : '不单调')
        : (desc === 0 ? '强单调（Q1<Q2<…<Q5）' : desc <= 1 ? '较单调' : '不单调');
      kpi('分层单调性', monoTxt, '五分位年化排序', desc >= 4 || desc === 0);
    }
    card.appendChild(kpis);
    card.appendChild(h('p', 'mf-sub', '判读标准：|IC均值|≥0.03 且 |ICIR|≥0.3 为有效。分层单调性：五层年化严格按因子排序（方向修正后）为"强单调"，说明收益随因子值连续变化而非仅两端有效。'));
  } else {
    card.appendChild(h('p', 'mf-sub', '有效周数不足，无法计算IC统计。'));
  }

  /* --- 图1：IC 时序 --- */
  card.appendChild(h('div', 'mf-doc-sec', '二、IC 时序：周度IC与滚动均值'));
  function chartBox(html) {
    var b = h('div');
    b.innerHTML = html;
    return b;
  }
  if (dated.ics.length > 5) {
    var s1 = [
      { label: '周度IC（原始）', color: '#cbd5e1', values: dated.ics, width: 1 },
      { label: '滚动13周IC', color: PALETTE[0], values: rollMean(dated.ics, 13), width: 2.2 },
      { label: '滚动52周IC', color: PALETTE[1], values: rollMean(dated.ics, 52), width: 1.8 }
    ];
    card.appendChild(chartBox(svgLine(name + ' · ' + GROUPS[gi] + '组 周度IC（原始，未按方向修正）', s1, { dates: dated.dates, height: 300 })));
    card.appendChild(h('p', 'mf-sub', '浅灰=单周IC噪声；红线=季度滚动均值（短期有效性）；蓝线=年度滚动均值（长期趋势）。滚动线持续位于0上方（按+1方向）或下方（按−1方向）说明因子在该时期稳定有效；穿越0则提示因子衰减或方向切换。'));
  } else {
    card.appendChild(h('p', 'mf-sub', '有效周数不足，无法绘制IC时序。'));
  }

  /* --- 图2：累计IC --- */
  card.appendChild(h('div', 'mf-doc-sec', '三、累计IC（按方向修正）'));
  if (dated.ics.length > 5) {
    var cum = [0];
    for (var ci = 0; ci < dated.ics.length; ci++) cum.push(cum[ci] + dir * dated.ics[ci]);
    var s2 = [{ label: '累计IC（方向×周度IC累加）', color: PALETTE[4], values: cum, width: 2 }];
    card.appendChild(chartBox(svgLine(name + ' · ' + GROUPS[gi] + '组 累计IC', s2, { dates: dated.dates, height: 260 })));
    card.appendChild(h('p', 'mf-sub', '累计IC = Σ(方向×周度IC)。单调上行=该方向下因子持续贡献预测力；走平=失效期；下行=方向错误。期末累计IC/周数≈方向修正后IC均值。'));
  }

  /* --- 图3：五分位分层 --- */
  card.appendChild(h('div', 'mf-doc-sec', '四、五分位分层回测：因子单调性'));
  if (qa) {
    var namesQ = ['Q1(因子最高20%)', 'Q2', 'Q3', 'Q4', 'Q5(因子最低20%)'];
    var s3 = [];
    for (var q2 = 0; q2 < 5; q2++) {
      var nav = [1];
      for (var t = 0; t < qa.layers[q2].length; t++) nav.push(nav[t] * (1 + qa.layers[q2][t]));
      s3.push({ label: namesQ[q2] + ' 年化' + fmtPctS(qa.anns[q2], 1), color: PALETTE[q2], values: nav, width: q2 === 0 || q2 === 4 ? 2.2 : 1.3 });
    }
    var spreadNav = [1];
    for (var t2 = 0; t2 < qa.layers[0].length; t2++) spreadNav.push(spreadNav[t2] * (1 + (qa.layers[0][t2] - qa.layers[4][t2])));
    s3.push({ label: 'Q1−Q5 多空', color: '#111827', values: spreadNav, width: 1.6 });
    card.appendChild(chartBox(svgLine(name + ' · ' + GROUPS[gi] + '组 五分位净值（' + qa.weeks + '周，等权，未计成本）', s3, { height: 340 })));
    card.appendChild(h('p', 'mf-sub', '按因子值分5层、各层等权、每周再平衡。方向+1时多头层=Q1，方向−1时多头层=Q5。若五层净值随因子值有序排开（阶梯状），因子具备单调选券能力；若仅两端分开而中间层缠绕，因子只在极值处有效。多空线持续上行=可对冲的稳定alpha。'));
  } else {
    card.appendChild(h('p', 'mf-sub', '样本不足，无法做分层检验。'));
  }

  /* --- 图4：最新截面分布 --- */
  card.appendChild(h('div', 'mf-doc-sec', '五、最新截面分布'));
  if (hist) {
    var med = medianOf(hist.vals);
    var q25 = quantileOf(hist.vals, 0.25), q75 = quantileOf(hist.vals, 0.75);
    var fmt = function (v) { return Math.abs(v) >= 100 ? v.toFixed(0) : v.toFixed(2); };
    var marks = [
      { v: q25, label: 'P25 ' + fmt(q25), color: '#94a3b8' },
      { v: med, label: '中位 ' + fmt(med), color: '#b9922e' },
      { v: q75, label: 'P75 ' + fmt(q75), color: '#94a3b8' }
    ];
    card.appendChild(chartBox(svgHist(name + ' · ' + GROUPS[gi] + '组 最新截面分布（' + hist.date + '，' + hist.vals.length + '/' + hist.pool + '只有值）', hist.vals, { marks: marks, fmt: fmt })));
    card.appendChild(h('p', 'mf-sub', '该组样本池在最新信号日的因子值分布。分布形态提示：双峰=组内存在两类券（如双低策略中的高/低平价簇）；长右尾=少数极端券，MAD去极值后会被压缩；当前打分取的是分布一端的前20%（按方向），即图上最左或最右侧的样本。'));
  } else {
    card.appendChild(h('p', 'mf-sub', '最新截面无有效样本。'));
  }

  /* --- 分年度IC表 --- */
  card.appendChild(h('div', 'mf-doc-sec', '六、分年度IC：因子衰减检查'));
  var ys = yearlyICStats(dated);
  if (ys.length) {
    var ytb = h('table', 'mf-table');
    ytb.innerHTML = '<thead><tr><th>年份</th><th class="mf-num">IC均值</th><th class="mf-num">方向修正后</th><th class="mf-num">IC胜率</th><th class="mf-num">有效周数</th><th>当年判读</th></tr></thead>';
    var yb = h('tbody');
    ys.forEach(function (y) {
      var adj = dir * y.mean;
      var yv = Math.abs(adj) >= 0.03 ? '有效' : (Math.abs(adj) >= 0.015 ? '弱有效' : '无效');
      var tr = h('tr');
      tr.appendChild(h('td', 'mf-k', y.year));
      var td0 = h('td', 'mf-num', fmtN(y.mean, 4));
      td0.style.background = icColor(y.mean);
      td0.style.color = Math.abs(y.mean) > 0.05 ? '#fff' : '#222';
      tr.appendChild(td0);
      var td1 = h('td', 'mf-num', fmtN(adj, 4));
      td1.style.background = icColor(adj);
      td1.style.color = Math.abs(adj) > 0.05 ? '#fff' : '#222';
      tr.appendChild(td1);
      tr.appendChild(h('td', 'mf-num', fmtPct(dir > 0 ? y.pos : 1 - y.pos, 0)));
      tr.appendChild(h('td', 'mf-num', String(y.n)));
      tr.appendChild(h('td', null, yv));
      yb.appendChild(tr);
    });
    ytb.appendChild(yb);
    card.appendChild(ytb);
    card.appendChild(h('p', 'mf-sub', '分年度看方向修正后IC是否持续同号：连续多年有效=稳健因子；只在个别年份有效=该时期的风格暴露；近年转弱=因子衰减，考虑降低权重或替换。'));
  } else {
    card.appendChild(h('p', 'mf-sub', '无有效周，无法做分年度统计。'));
  }

  holder.appendChild(card);
  if (scrollTo && holder.scrollIntoView) holder.scrollIntoView({ behavior: 'smooth', block: 'start' });
}

/* ------------------------------ 视图：③ 自创因子 ------------------------------ */
function vCustom() {
  var root = $('mf-view-custom');
  clear(root);
  var card = h('div', 'mf-card');
  card.appendChild(h('h3', null, '自创因子：用表达式组合现有字段'));
  card.appendChild(h('p', 'mf-sub', '表达式在每周信号日截面上逐券求值；非法值（log≤0、除0、缺失操作数）按缺失处理（打分时填0）。可引用内置字段与其他自创因子（不允许循环引用）。'));
  var syntax = h('div', 'mf-code');
  syntax.textContent = '字段：price, cb_value, bond_value, flat_prem, prem, prem_z3, ytm, dual_low, dl_z6, r_cv20, r_cb10, r_cb20, r120_z6, diff10, boll120, turn120, turn_month, turn5, cb_vol20, cv_vol20, rem_years, issue_size_yi, amount_avg3 …（完整名单见②因子库）\n运算：+ - * / ^ ( )    函数：log(x) abs(x) sqrt(x) neg(x) min(a,b) max(a,b) pow(a,b)\n示例：r_cb20 - r_cv20（转债跑赢正股）  log(issue_size_yi)（对数规模）  r_cb10 / max(turn5, 1)（单位换手动量）';
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

/* ------------------------------ 视图：④ IC验证 ------------------------------ */
function vIC() {
  var root = $('mf-view-ic');
  clear(root);
  var bar = h('div', 'mf-toolbar');
  var gtabs = h('div', 'mf-tabs');
  GROUPS.forEach(function (g, gi) {
    var b = h('button', 'mf-tab' + (gi === IC_GROUP ? ' on' : ''), g);
    b.onclick = function () { IC_GROUP = gi; vIC(); };
    gtabs.appendChild(b);
  });
  bar.appendChild(gtabs);
  root.appendChild(bar);
  var gi = IC_GROUP;

  /* 当前配置因子IC表 */
  var card = h('div', 'mf-card');
  card.appendChild(h('h3', null, GROUPS[gi] + ' · 当前配置因子周度IC（全样本期）'));
  var tb = h('table', 'mf-table');
  tb.innerHTML = '<thead><tr><th>因子</th><th class="mf-num">IC均值</th><th class="mf-num">ICIR</th><th class="mf-num">IC胜率</th><th class="mf-num">t值</th><th class="mf-num">有效周数</th><th>判读</th></tr></thead>';
  var tbody = h('tbody');
  var rowsData = [];
  CFG.sel[gi].forEach(function (p) {
    var arr = icSeries(gi, p.k);
    var st = icStats(arr);
    if (st) rowsData.push({ name: fieldName(p.k), dir: p.dir, st: st, key: p.k });
  });
  rowsData.push({ name: '【复合得分（当前配置）】', dir: 1, st: icStats(compositeICSeries(gi)), key: '__score' });
  rowsData.forEach(function (r) {
    var tr = h('tr', r.key === '__score' ? 'mf-row-score' : null);
    tr.appendChild(h('td', 'mf-k', r.name + (r.dir < 0 && r.key !== '__score' ? '（方向−1）' : '')));
    var td1 = h('td', 'mf-num', fmtN(r.st ? r.st.mean : null, 4));
    if (r.st) { td1.style.background = icColor(r.st.mean); td1.style.color = Math.abs(r.st.mean) > 0.05 ? '#fff' : '#222'; }
    tr.appendChild(td1);
    tr.appendChild(h('td', 'mf-num', r.st && r.st.icir != null ? fmtN(r.st.icir, 2) : '—'));
    tr.appendChild(h('td', 'mf-num', r.st ? fmtPct(r.st.pos, 0) : '—'));
    tr.appendChild(h('td', 'mf-num', r.st && r.st.t != null ? fmtN(r.st.t, 2) : '—'));
    tr.appendChild(h('td', 'mf-num', r.st ? String(r.st.n) : '—'));
    var verdict = '—';
    if (r.st) {
      var a = Math.abs(r.st.mean), ai = Math.abs(r.st.icir || 0);
      verdict = (a >= 0.03 && ai >= 0.3) ? '有效' : (a >= 0.015 ? '弱有效' : '无效');
      if ((r.st.mean < 0) !== (r.dir < 0) && r.key !== '__score' && a >= 0.03) verdict += '（注意：方向可能反了）';
    }
    tr.appendChild(h('td', null, verdict));
    tbody.appendChild(tr);
  });
  tb.appendChild(tbody);
  card.appendChild(tb);
  card.appendChild(h('p', 'mf-sub', '判读标准：|IC均值|≥0.03 且 |ICIR|≥0.3 为有效；若有效但方向与所选方向相反，回到②改方向。复合得分为最终判据。'));
  root.appendChild(card);

  /* 分层检验 */
  var card2 = h('div', 'mf-card');
  card2.appendChild(h('h3', null, '分层检验（五分位）'));
  var ctl = h('div', 'mf-toolbar');
  var lbl = h('label', 'mf-label', '因子：');
  var sel = h('select', 'mf-input');
  var opts = CFG.sel[gi].map(function (p) { return { k: p.k, n: fieldName(p.k) }; });
  opts.push({ k: '__score', n: '【复合得分】' });
  opts.forEach(function (o) {
    var op = h('option', null, o.n); op.value = o.k; sel.appendChild(op);
  });
  sel.value = '__score';
  ctl.appendChild(lbl); ctl.appendChild(sel);
  card2.appendChild(ctl);
  var holder = h('div');
  card2.appendChild(holder);
  root.appendChild(card2);
  function drawLayer() {
    clear(holder);
    var key = sel.value;
    var qa = quintileAnalysis(gi, key);
    if (!qa) { holder.appendChild(h('p', 'mf-sub', '样本不足')); return; }
    var series = [];
    var names = ['Q1(最高20%)', 'Q2', 'Q3', 'Q4', 'Q5(最低20%)'];
    for (var q = 0; q < 5; q++) {
      var nav = [1];
      for (var t = 0; t < qa.layers[q].length; t++) nav.push(nav[t] * (1 + qa.layers[q][t]));
      series.push({ label: names[q] + ' 年化' + fmtPctS(qa.anns[q], 1), color: PALETTE[q], values: nav, width: q === 0 || q === 4 ? 2.2 : 1.4 });
    }
    var spreadNav = [1];
    for (var t2 = 0; t2 < qa.layers[0].length; t2++) {
      spreadNav.push(spreadNav[t2] * (1 + (qa.layers[0][t2] - qa.layers[4][t2])));
    }
    series.push({ label: 'Q1−Q5 多空', color: '#111827', values: spreadNav, width: 1.6 });
    holder.innerHTML = svgLine(GROUPS[gi] + ' · ' + fieldName(key) + ' 五分位净值（' + qa.weeks + '周）', series, { dates: [] });
    var note = h('p', 'mf-sub');
    var dirNote = factorDir(key, gi) < 0 ? '该因子方向为−1时，预期多头层是Q5。' : '该因子方向为+1时，预期多头层是Q1。';
    note.textContent = dirNote + ' 单调性：' + fmtPctS(qa.anns[0], 1) + ' / ' + fmtPctS(qa.anns[1], 1) + ' / ' +
      fmtPctS(qa.anns[2], 1) + ' / ' + fmtPctS(qa.anns[3], 1) + ' / ' + fmtPctS(qa.anns[4], 1) +
      '；多空年化 ' + fmtPctS(Math.pow(spreadNav[spreadNav.length - 1], CONSTS.weeksPerYear / qa.weeks) - 1, 1) + '。';
    holder.appendChild(note);
  }
  sel.onchange = drawLayer;
  drawLayer();
}

/* ------------------------------ 视图：⑤ 组合回测 ------------------------------ */
function vBacktest() {
  var root = $('mf-view-bt');
  clear(root);
  var bar = h('div', 'mf-toolbar');
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
  bar.appendChild(mkSel('组合范围', [['combo', '三类合成（各1/3）'], [0, '仅偏债型'], [1, '仅平衡型'], [2, '仅偏股型']], CFG.params.mode, function (v) { CFG.params.mode = (v === 'combo') ? 'combo' : Number(v); }));
  var tcWrap = h('label', 'mf-ctl');
  var tcCb = h('input'); tcCb.type = 'checkbox'; tcCb.checked = CFG.params.turnover;
  var tcSel = h('select', 'mf-input');
  [[0.3, '≤30%'], [0.5, '≤50%'], [0.7, '≤70%']].forEach(function (o) { var op = h('option', null, o[1]); op.value = String(o[0]); tcSel.appendChild(op); });
  tcSel.value = String(CFG.params.turnoverLimit);
  tcCb.onchange = function () { CFG.params.turnover = tcCb.checked; saveCfg(); };
  tcSel.onchange = function () { CFG.params.turnoverLimit = Number(tcSel.value); saveCfg(); };
  tcWrap.appendChild(tcCb);
  tcWrap.appendChild(h('span', null, '控换手'));
  tcWrap.appendChild(tcSel);
  bar.appendChild(tcWrap);
  bar.appendChild(mkSel('成本(bp/边)', [[0, '0'], [5, '5（默认）'], [10, '10'], [15, '15'], [20, '20']], CFG.params.costBps, function (v) { CFG.params.costBps = Number(v); }));
  var runB = h('button', 'mf-btn mf-btn-primary', '运行回测');
  bar.appendChild(runB);
  root.appendChild(bar);

  var out = h('div', 'mf-bt-out');
  root.appendChild(out);

  function kpiCard(label, value, sub, cls) {
    var c = h('div', 'mf-kpi' + (cls ? ' ' + cls : ''));
    c.appendChild(h('div', 'mf-kpi-l', label));
    c.appendChild(h('div', 'mf-kpi-v', value));
    if (sub) c.appendChild(h('div', 'mf-kpi-s', sub));
    return c;
  }
  function perfTable(title, m, idxM) {
    var card = h('div', 'mf-card');
    card.appendChild(h('h3', null, title));
    var tb = h('table', 'mf-table');
    var rows = [
      ['回测总收益率', fmtPctS(m.total), fmtPctS(idxM.total)],
      ['年化收益率', fmtPctS(m.ann), fmtPctS(idxM.ann)],
      ['年化超额收益', fmtPctS(m.ann - idxM.ann), '—'],
      ['年化波动率', fmtPct(m.vol), fmtPct(idxM.vol)],
      ['最大回撤', fmtPct(m.mdd), fmtPct(idxM.mdd)],
      ['夏普比率', fmtN(m.sharpe), fmtN(idxM.sharpe)],
      ['卡玛比率', fmtN(m.calmar), fmtN(idxM.calmar)],
      ['周度胜率', fmtPct(m.winRate), fmtPct(idxM.winRate)],
      ['盈亏比', fmtN(m.pl), fmtN(idxM.pl)],
      ['调仓周数', String(m.weeks || '—'), String(idxM.weeks || '—')]
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
    var ex = m.ann - im.ann;
    var kpis = h('div', 'mf-kpis');
    kpis.appendChild(kpiCard('年化收益', fmtPctS(m.ann), '指数 ' + fmtPctS(im.ann)));
    kpis.appendChild(kpiCard('年化超额', fmtPctS(ex), null, ex >= 0 ? 'mf-kpi-good' : 'mf-kpi-bad'));
    kpis.appendChild(kpiCard('最大回撤', fmtPct(m.mdd), null, m.mdd > -0.1 ? 'mf-kpi-good' : ''));
    kpis.appendChild(kpiCard('夏普比率', fmtN(m.sharpe), null, (m.sharpe || 0) >= 1 ? 'mf-kpi-good' : ''));
    kpis.appendChild(kpiCard('周度胜率', fmtPct(m.winRate), '盈亏比 ' + fmtN(m.pl)));
    var avgTO = mean(bt.turnovers);
    kpis.appendChild(kpiCard('周均换手(双边)', fmtPct(avgTO), '耗时' + bt.ms + 'ms'));
    out.appendChild(kpis);

    /* 净值曲线 */
    var series = [
      { label: '本组合（期末 ' + fmtN(bt.combo[bt.combo.length - 1], 3) + '）', color: PALETTE[0], values: bt.combo, width: 2.4 },
      { label: '中证转债指数（期末 ' + fmtN(bt.idx[bt.idx.length - 1], 3) + '）', color: PALETTE[1], values: bt.idx, width: 1.8 }
    ];
    if (REF.mf_combo && CFG.params.mode === 'combo') {
      series.push({ label: '报告默认组合（Python精确版）', color: PALETTE[3], values: REF.mf_combo.nav.slice(0, bt.combo.length), width: 1.6 });
    }
    var chartCard = h('div', 'mf-card');
    chartCard.innerHTML = svgLine('组合净值对比（周度，成本' + CFG.params.costBps + 'bp/边' + (CFG.params.turnover ? '，控换手≤' + Math.round(CFG.params.turnoverLimit * 100) + '%' : '') + '）', series, { dates: bt.dates });
    out.appendChild(chartCard);

    /* 绩效表 */
    out.appendChild(perfTable('全区间绩效（vs 中证转债指数）', m, im));

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
    if (REF.mf_combo && CFG.params.mode === 'combo') {
      var refN = REF.mf_combo.nav, myN = bt.combo;
      var n = Math.min(refN.length, myN.length);
      var diffs = [];
      for (var i = 1; i < n; i++) diffs.push(myN[i] / myN[i - 1] - refN[i] / refN[i - 1]);
      var te = stdev(diffs) * Math.sqrt(CONSTS.weeksPerYear);
      var note = h('div', 'mf-note');
      note.appendChild(h('div', null, '与报告默认组合（Python精确版）对照：期末本组合 ' + fmtN(myN[n - 1], 3) + ' vs 精确版 ' + fmtN(refN[n - 1], 3) +
        '，跟踪误差(年化) ' + fmtPct(te) + '。'));
      note.appendChild(h('div', 'mf-sub', '差异来源：浏览器版为周度速算（权重漂移近似计成本、摘牌按最后价近似、控换手为启发式），Python版为日频账本+LP精确解。配置相同时两者趋势一致；正式结果以⑥导出后 Python 复核为准。'));
      out.appendChild(note);
    }

    /* 最新信号持仓（下周执行名单） */
    var lastCard = h('div', 'mf-card');
    lastCard.appendChild(h('h3', null, '最新信号持仓（' + (WEEKS[WEEKS.length - 1].d) + ' 信号 · 供下周执行预览）'));
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
    for (var s2 = 0; s2 < bt.sleeves.length; s2++) {
      var sl = bt.sleeves[s2];
      for (var w2 = 0; w2 < sl.holdings.length; w2++) {
        if (sl.holdings[w2]) recs.push({ s: s2, w: w2, hold: sl.holdings[w2] });
      }
    }
    recs.forEach(function (r, i) {
      var op = h('option', null, GROUPS[r.hold.group] + ' · ' + r.hold.d + '（信号日）');
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
      htable.appendChild(h('p', 'mf-sub', '信号日 ' + r.hold.d + ' · 执行日 ' + r.hold.e + ' · ' + r.hold.list.length + ' 只等权'));
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
  else out.appendChild(h('p', 'mf-sub', '点击「运行回测」：按当前②③的因子配置与上方参数，在浏览器内完成 ' + (WEEKS.length - 1) + ' 周的周度组合模拟（含成本与换手统计）。'));
}
function exportHoldingsCsv() {
  if (!LAST_BT) return;
  var lines = ['sleeve_group,signal_date,exec_date,code,name,weight,composite_score'];
  LAST_BT.sleeves.forEach(function (sl) {
    sl.holdings.forEach(function (hd) {
      if (!hd) return;
      hd.list.forEach(function (x) {
        lines.push([GROUPS[hd.group], hd.d, hd.e, BONDS[x.bi][0], BONDS[x.bi][1],
        x.w.toFixed(6), x.score.toFixed(4)].join(','));
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
  card.appendChild(h('h3', null, '导出配置 → Python 精确复核'));
  card.appendChild(h('p', 'mf-sub', '将当前因子选择、自创因子表达式与回测参数导出为 JSON，交给 run_lab_config.py 用官方日频引擎精确复核，产出正式回测档案（净值曲线PNG+CSV、全区间+分年度绩效、每次调仓持仓名单与权重、参数存档），满足正式回测交付要求。'));
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
  jc.appendChild(br);
  root.appendChild(jc);

  /* 运行指令 */
  var rc = h('div', 'mf-card');
  rc.appendChild(h('h3', null, '复核步骤'));
  var code = h('div', 'mf-code');
  code.textContent = '# 1) 将 mf_lab_config.json 保存到项目根目录（与 cb_multifactor_backtest.py 同级）\n' +
    '# 2) 运行精确复核（日频引擎 · LP控换手 · 摘牌退出 · 输出正式档案）\n' +
    'python3 run_lab_config.py --config mf_lab_config.json\n\n' +
    '# 输出目录：backtest_results/mf_lab/<配置名>/\n' +
    '#   nav_curve.csv / nav_vs_index.png   净值曲线（vs 中证转债指数 000832）\n' +
    '#   performance_summary.csv            全区间 + 分年度绩效（总收益/年化/回撤/夏普/胜率/盈亏比/波动）\n' +
    '#   rebalance_holdings.csv             每次调仓持仓名单与权重\n' +
    '#   run_meta.json                      本次配置与口径存档';
  rc.appendChild(code);
  rc.appendChild(h('p', 'mf-sub', 'Python 复核与浏览器速算的差异见「① 方法思路」；两者结论方向应一致，正式结论以 Python 版为准。'));
  root.appendChild(rc);
}

/* ------------------------------ 视图路由 ------------------------------ */
var VIEWS = [
  ['method', '① 方法思路'],
  ['library', '② 因子库'],
  ['custom', '③ 自创因子'],
  ['ic', '④ IC验证'],
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
function ensureData(cb) {
  if (dataLoaded) { cb(); return; }
  if (dataLoading) return;
  dataLoading = true;
  var msg = $('mf-load-msg');
  if (msg) msg.textContent = '正在加载多因子数据集（约22MB，首次需数秒）…';
  var s = document.createElement('script');
  s.src = 'multifactor_lab_data.js';
  s.onload = function () {
    try { init(); cb(); }
    catch (e) {
      if (msg) { msg.textContent = '初始化失败：' + e.message; }
      console.error(e);
    }
  };
  s.onerror = function () {
    dataLoading = false;
    if (msg) msg.textContent = '数据文件 multifactor_lab_data.js 加载失败：请确认与页面同目录（发布页需随站点一起部署）。';
  };
  document.head.appendChild(s);
}
function init() {
  D = window.MF_LAB_DATA;
  if (!D) throw new Error('MF_LAB_DATA 缺失');
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
    meta.appendChild(h('span', 'mf-badge', '信号区间 ' + D.period[0] + ' ~ ' + D.period[1]));
    meta.appendChild(h('span', 'mf-badge', WEEKS.length + ' 周截面'));
    meta.appendChild(h('span', 'mf-badge', BONDS.length + ' 只转债'));
    meta.appendChild(h('span', 'mf-badge', FIELDS.length + ' 个字段'));
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
window.__mfLabOnShown = function () {
  if (booted) return;
  booted = true;
  ensureData(function () { });
};
})();
