/* Factor research statistics. Price-return diagnostics, not an executable backtest. */
(function (root, factory) {
  'use strict';
  var api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  if (root) root.MFResearch = api;
})(typeof window !== 'undefined' ? window : globalThis, function () {
  'use strict';
  var VERSION = 'factor-research/1.0.0';
  function finite(x) { return typeof x === 'number' && Number.isFinite(x); }
  function mean(a) { var b = a.filter(finite); return b.length ? b.reduce(function (x, y) { return x + y; }, 0) / b.length : null; }
  function rankAvg(a) {
    var order = a.map(function (_, i) { return i; }).sort(function (i, j) { return a[i] - a[j]; }), out = new Array(a.length);
    for (var i = 0; i < order.length;) {
      var j = i + 1;
      while (j < order.length && a[order[j]] === a[order[i]]) j++;
      for (var k = i; k < j; k++) out[order[k]] = (i + j + 1) / 2;
      i = j;
    }
    return out;
  }
  function pearson(x, y) {
    if (x.length < 2 || x.length !== y.length) return null;
    var mx = mean(x), my = mean(y), xx = 0, yy = 0, xy = 0;
    for (var i = 0; i < x.length; i++) { var dx = x[i] - mx, dy = y[i] - my; xx += dx * dx; yy += dy * dy; xy += dx * dy; }
    return xx > 0 && yy > 0 ? Math.max(-1, Math.min(1, xy / Math.sqrt(xx * yy))) : null;
  }
  function spearman(xs, ys, minPairs) {
    var x = [], y = [];
    for (var i = 0; i < xs.length; i++) if (finite(xs[i]) && finite(ys[i])) { x.push(xs[i]); y.push(ys[i]); }
    return x.length >= (minPairs == null ? 2 : minPairs) ? pearson(rankAvg(x), rankAvg(y)) : null;
  }
  // Two-sided Gaussian approximation. No claim of exact finite-sample inference.
  function normalP(t) {
    var x = Math.abs(t), z = 1 / (1 + 0.2316419 * x);
    var tail = Math.exp(-x * x / 2) / Math.sqrt(2 * Math.PI) * z * (0.319381530 + z * (-0.356563782 + z * (1.781477937 + z * (-1.821255978 + z * 1.330274429))));
    return Math.max(0, Math.min(1, 2 * tail));
  }
  function hacSummary(periods, opts) {
    opts = opts || {};
    var values = periods.map(function (p, i) { return typeof p === 'number' || p == null ? { ic: p, rawIC: p, grid: i } : Object.assign({}, p, { grid: finite(p.grid) ? p.grid : i }); }).filter(function (p) { return finite(p.ic); });
    var n = values.length, avg = mean(values.map(function (p) { return p.ic; }));
    var raw = mean(values.map(function (p) { return finite(p.rawIC) ? p.rawIC : p.ic; }));
    var minPeriods = opts.minPeriods == null ? 20 : opts.minPeriods;
    var requestedLag = Math.max(0, opts.lag || 0), gridSpan = n ? Math.max.apply(null, values.map(function (p) { return p.grid; })) - Math.min.apply(null, values.map(function (p) { return p.grid; })) : 0;
    var lag = Math.min(gridSpan, Math.max(requestedLag, Math.floor(4 * Math.pow(Math.max(1, n) / 100, 2 / 9))));
    var ss = 0, weighted = 0;
    if (n) values.forEach(function (p) { ss += Math.pow(p.ic - avg, 2); });
    weighted = ss;
    for (var i = 0; i < n; i++) for (var j = i + 1; j < n; j++) {
      var distance = Math.abs(values[j].grid - values[i].grid);
      if (distance > 0 && distance <= lag) weighted += 2 * (1 - distance / (lag + 1)) * (values[i].ic - avg) * (values[j].ic - avg);
    }
    var sd = n > 1 ? Math.sqrt(ss / (n - 1)) : null;
    // Intercept-only Newey-West covariance with n/(n-1) correction. Missing IC grid slots are preserved.
    var se = n > 1 ? Math.sqrt(Math.max(0, weighted) / (n * n) * n / (n - 1)) : null;
    var t = finite(se) && se > 1e-14 ? avg / se : null;
    var descriptive = n < minPeriods || t == null;
    var out = {
      rawMeanIC: raw, meanIC: avg, sdIC: sd, icir: finite(sd) && sd > 1e-14 ? avg / sd : null,
      positiveShare: n ? values.filter(function (p) { return p.ic > 0; }).length / n : null,
      n: n, hacSE: se, hacT: t, ci95: finite(se) ? [avg - 1.959963984540054 * se, avg + 1.959963984540054 * se] : null,
      pValue: !descriptive ? normalP(t) : null, descriptive: descriptive, lag: lag, requestedLag: requestedLag,
      gridSpan: gridSpan, missingGridPeriods: n ? gridSpan + 1 - n : 0
    };
    out.icMean = out.meanIC; out.icIR = out.icir; out.icPositiveRate = out.positiveShare; out.periods = n; out.tStat = t;
    return out;
  }
  function bh(pValues) {
    var valid = pValues.map(function (p, i) { return { p: p, i: i }; }).filter(function (o) { return finite(o.p) && o.p >= 0 && o.p <= 1; }).sort(function (a, b) { return a.p - b.p; });
    var out = pValues.map(function () { return null; }), next = 1;
    for (var j = valid.length - 1; j >= 0; j--) { next = Math.min(next, valid[j].p * valid.length / (j + 1)); out[valid[j].i] = next; }
    return out;
  }
  function residualize(values, columns) {
    var valid = [];
    values.forEach(function (x, i) { if (finite(x) && columns.every(function (c) { return finite(c[i]); })) valid.push(i); });
    var out = values.map(function () { return null; });
    if (valid.length < Math.max(3, columns.length + 3)) return out;
    var y = valid.map(function (i) { return values[i]; }), ym = mean(y), r = y.map(function (v) { return v - ym; }), basis = [];
    columns.forEach(function (col) {
      var v = valid.map(function (i) { return col[i]; }), m = mean(v); v = v.map(function (x) { return x - m; });
      var originalNorm = Math.sqrt(v.reduce(function (s, x) { return s + x * x; }, 0));
      basis.forEach(function (q) { var p = v.reduce(function (s, x, j) { return s + x * q[j]; }, 0); v = v.map(function (x, j) { return x - p * q[j]; }); });
      var norm = Math.sqrt(v.reduce(function (s, x) { return s + x * x; }, 0));
      if (norm > 1e-10 * Math.max(1, originalNorm)) basis.push(v.map(function (x) { return x / norm; }));
    });
    basis.forEach(function (q) { var p = r.reduce(function (s, x, j) { return s + x * q[j]; }, 0); r = r.map(function (x, j) { return x - p * q[j]; }); });
    var residualNorm = Math.sqrt(r.reduce(function (s, x) { return s + x * x; }, 0)), originalYNorm = Math.sqrt(y.reduce(function (s, x) { return s + Math.pow(x - ym, 2); }, 0));
    // Numerical dust must not manufacture ranks after a control exactly explains the factor.
    if (residualNorm <= 1e-10 * Math.max(1, originalYNorm)) r = r.map(function () { return 0; });
    valid.forEach(function (i, j) { out[i] = r[j]; }); return out;
  }
  function quantileMembership(values, direction) {
    var ids = [], vals = [], out = values.map(function () { return null; });
    values.forEach(function (x, i) { if (finite(x)) { ids.push(i); vals.push((direction === -1 ? -1 : 1) * x); } });
    rankAvg(vals).forEach(function (rank, i) { out[ids[i]] = Math.min(5, Math.floor(5 * (rank - 0.5) / vals.length) + 1); });
    return out;
  }
  function create(data, hooks) {
    hooks = hooks || {};
    var fields = data.fields || [], fieldIndex = {}, fieldMeta = {};
    fields.forEach(function (f, i) { fieldIndex[f.k] = i + 3; fieldMeta[f.k] = f; });
    var weeks = data.weeks || [], frames = ((data.market || {}).frames || []).slice().sort(function (a, b) { return a.d.localeCompare(b.d); });
    var frameIndex = {}, quoteCache = new Map(), labelCache = new Map();
    frames.forEach(function (f, i) { frameIndex[f.d] = i; });
    function value(row, key, week) { var x = hooks.valueGetter ? hooks.valueGetter(row, key, week) : row[fieldIndex[key]]; return finite(x) ? x : null; }
    function quotes(index) {
      if (index == null || !frames[index]) return null;
      if (!quoteCache.has(index)) quoteCache.set(index, new Map((frames[index].q || []).map(function (q) { return [q[0], q]; })));
      return quoteCache.get(index);
    }
    function normalize(options) {
      var o = Object.assign({}, options || {});
      o.key = o.key || (fields[0] || {}).k; o.group = o.group == null ? 'all' : o.group;
      if (o.group !== 'all') o.group = Number(o.group);
      o.horizon = Number(o.horizon || 5); if ([1, 5, 10, 20, 60].indexOf(o.horizon) < 0) throw Error('研究收益期限须为 1 / 5 / 10 / 20 / 60 个交易日');
      o.direction = o.direction === -1 ? -1 : 1;
      o.start = o.start || (weeks[0] || {}).d || ''; o.end = o.end || (frames[frames.length - 1] || {}).d || '';
      if (o.start > o.end) throw Error('研究起始日期不能晚于结束日期');
      o.split = o.split || o.splitDate || null; o.rolling = Number(o.rolling || o.rollingWindow || 26);
      if ([26, 52].indexOf(o.rolling) < 0) o.rolling = 26;
      o.minPairs = Math.max(3, Number(o.minPairs || o.minNames || 10)); o.minPeriods = Math.max(3, Number(o.minPeriods || 20));
      o.controls = o.controls === 'price_parity_size' ? ['price', 'cb_value', 'issue_size_yi'] : Array.isArray(o.controls) ? o.controls.filter(function (k, i, a) { return a.indexOf(k) === i; }) : [];
      o.controls.forEach(function (key) { if (['price', 'cb_value', 'issue_size_yi'].indexOf(key) < 0) throw Error('仅支持价格、平价、发行规模的截面控制'); });
      o.lag = Math.max(Math.ceil(o.horizon / 5) - 1, Number(o.lag) || 0);
      return o;
    }
    function eligibleRows(week, o) { return (week.rows || []).filter(function (r) { return o.group === 'all' || r[1] === o.group; }); }
    function factorValues(week, rows, o) {
      var values;
      if (o.key === '__score') {
        var scores = new Map();
        if (hooks.scoreGetter) (o.group === 'all' ? [0, 1, 2] : [o.group]).forEach(function (g) {
          var result = hooks.scoreGetter(week, g) || {};
          (result.rows || []).forEach(function (r, i) { var x = (result.scores || [])[i]; if (finite(x)) scores.set(r[0], x); });
        });
        values = rows.map(function (r) { return scores.has(r[0]) ? scores.get(r[0]) : null; });
      } else values = rows.map(function (r) { return value(r, o.key, week); });
      var rawFactorN = values.filter(finite).length;
      if (o.controls.length) values = residualize(values, o.controls.map(function (key) { return rows.map(function (r) { var x = value(r, key, week); return x > 0 ? Math.log(x) : null; }); }));
      return { values: values, rawFactorN: rawFactorN };
    }
    function labels(week, horizon) {
      var cacheKey = week.e + ':' + horizon;
      if (labelCache.has(cacheKey)) return labelCache.get(cacheKey);
      var entryIndex = frameIndex[week.e], exitIndex = entryIndex == null ? null : entryIndex + horizon;
      var entry = quotes(entryIndex), exit = quotes(exitIndex), result = { entry: entry, exit: exit, entryIndex: entryIndex, exitIndex: exitIndex, labelEnd: frames[exitIndex] ? frames[exitIndex].d : null, returns: new Map() };
      if (entry && exit) entry.forEach(function (q, id) { var e = exit.get(id); if (q[1] > 0 && finite(q[1]) && e && e[1] > 0 && finite(e[1])) result.returns.set(id, e[1] / q[1] - 1); });
      labelCache.set(cacheKey, result); return result;
    }
    function cover(periods, omitted) {
      var sum = function (key) { return periods.reduce(function (s, p) { return s + (p[key] || 0); }, 0); };
      var universeN = sum('universeN'), factorN = sum('factorN'), pairN = sum('pairN');
      return { periods: periods.length, universeN: universeN, rawFactorN: sum('rawFactorN'), factorN: factorN, pairN: pairN,
        factorCoverage: universeN ? factorN / universeN : null, labelCoverage: factorN ? pairN / factorN : null,
        meanFactorCoverage: mean(periods.map(function (p) { return p.factorCoverage; })), meanLabelCoverage: mean(periods.map(function (p) { return p.labelCoverage; })),
        meanPairN: periods.length ? pairN / periods.length : null, meanUniverseN: periods.length ? universeN / periods.length : null,
        missingEntryN: sum('missingEntryN'), missingExitN: sum('missingExitN'), entryNotTradeableN: sum('entryNotTradeableN'), omittedHorizonPeriods: omitted || 0 };
    }
    function qAggregate(periods) {
      return [1, 2, 3, 4, 5].map(function (q) {
        var qs = periods.map(function (p) { return p.quantiles[q - 1]; }), signalN = qs.reduce(function (s, x) { return s + x.signalN; }, 0), pairN = qs.reduce(function (s, x) { return s + x.pairN; }, 0);
        return { q: q, signalN: signalN, pairN: pairN, coverage: signalN ? pairN / signalN : null, meanReturn: mean(qs.map(function (x) { return x.meanReturn; })), periods: qs.filter(function (x) { return finite(x.meanReturn); }).length };
      });
    }
    function aggregate(periods, o, omitted) {
      var summary = hacSummary(periods, o);
      summary.meanSpread = mean(periods.map(function (p) { return p.spread; })); summary.meanTopExcess = mean(periods.map(function (p) { return p.topExcess; })); summary.meanMonotonicity = mean(periods.map(function (p) { return p.monotonicity; }));
      return { summary: summary, coverage: cover(periods, omitted), quantiles: qAggregate(periods) };
    }
    function grouped(periods, o, length) {
      var groups = {};
      periods.forEach(function (p) { var key = p.d.slice(0, length); (groups[key] || (groups[key] = [])).push(p); });
      return Object.keys(groups).sort().map(function (key) { var a = aggregate(groups[key], o); return Object.assign({ period: key }, a.summary, { summary: a.summary, coverage: a.coverage, quantiles: a.quantiles }); });
    }
    function analyze(options) {
      var o = normalize(options), periods = [], omitted = 0, missingExecutionPeriods = 0;
      weeks.forEach(function (week, grid) {
        if (week.d < o.start || week.d > o.end) return;
        var lab = labels(week, o.horizon);
        if (!lab.labelEnd || lab.labelEnd > o.end) { omitted++; if (lab.entryIndex == null) missingExecutionPeriods++; return; }
        var rows = eligibleRows(week, o), f = factorValues(week, rows, o), xs = f.values, ys = rows.map(function (r) { return lab.returns.has(r[0]) ? lab.returns.get(r[0]) : null; });
        var membership = quantileMembership(xs, o.direction), factorN = xs.filter(finite).length, pairN = 0, missingEntryN = 0, missingExitN = 0, entryNotTradeableN = 0, pool = [];
        rows.forEach(function (r, i) {
          if (!finite(xs[i])) return;
          var entry = lab.entry && lab.entry.get(r[0]), exit = lab.exit && lab.exit.get(r[0]);
          if (!(entry && finite(entry[1]) && entry[1] > 0)) missingEntryN++;
          if (!(exit && finite(exit[1]) && exit[1] > 0)) missingExitN++;
          if (entry && entry[2] !== 1) entryNotTradeableN++;
          if (finite(ys[i])) { pairN++; pool.push(ys[i]); }
        });
        var rawIC = spearman(xs, ys, o.minPairs), qs = [1, 2, 3, 4, 5].map(function (q) {
          var returns = [], signalN = 0;
          membership.forEach(function (m, i) { if (m === q) { signalN++; if (finite(ys[i])) returns.push(ys[i]); } });
          return { q: q, signalN: signalN, pairN: returns.length, coverage: signalN ? returns.length / signalN : null, meanReturn: mean(returns) };
        });
        var poolReturn = mean(pool), lo = qs[0].meanReturn, hi = qs[4].meanReturn;
        periods.push({ d: week.d, e: week.e, grid: grid, labelEnd: lab.labelEnd, universeN: rows.length, rawFactorN: f.rawFactorN, factorN: factorN, pairN: pairN,
          factorCoverage: rows.length ? factorN / rows.length : null, labelCoverage: factorN ? pairN / factorN : null, rawIC: rawIC, ic: rawIC == null ? null : o.direction * rawIC,
          missingEntryN: missingEntryN, missingExitN: missingExitN, entryNotTradeableN: entryNotTradeableN, quantiles: qs,
          spread: finite(lo) && finite(hi) ? hi - lo : null, topExcess: finite(hi) && finite(poolReturn) ? hi - poolReturn : null, poolReturn: poolReturn,
          monotonicity: qs.every(function (q) { return finite(q.meanReturn); }) ? spearman([1, 2, 3, 4, 5], qs.map(function (q) { return q.meanReturn; })) : null });
      });
      // Include any additional overlapping signal slots caused by holiday-shortened weeks.
      var maxOverlap = o.lag;
      periods.forEach(function (p, i) { for (var j = i + 1; j < periods.length && periods[j].e < p.labelEnd; j++) maxOverlap = Math.max(maxOverlap, periods[j].grid - p.grid); });
      o.lag = maxOverlap;
      var result = aggregate(periods, o, omitted);
      result.options = o; result.periods = periods;
      result.rolling = periods.map(function (p, i) {
        var win = periods.slice(Math.max(0, i + 1 - o.rolling), i + 1), valid = win.filter(function (x) { return finite(x.ic); });
        var complete = win.length === o.rolling && valid.length === o.rolling && win[win.length - 1].grid - win[0].grid === o.rolling - 1;
        return { d: p.d, n: valid.length, complete: complete, meanIC: complete ? mean(valid.map(function (x) { return x.ic; })) : null };
      });
      result.annual = grouped(periods, o, 4); result.monthly = grouped(periods, o, 7);
      result.split = null;
      if (o.split) {
        var train = periods.filter(function (p) { return p.d <= o.split && p.labelEnd <= o.split; }), validation = periods.filter(function (p) { return p.d > o.split; });
        result.split = { date: o.split, purgedPeriods: periods.length - train.length - validation.length, train: aggregate(train, o), validation: aggregate(validation, o), directionLocked: true };
      }
      result.method = [
        '信号使用当期因子；收益为执行日收盘到其后 H 个交易日收盘的价格收益，不含票息、费用和现金流，也不保证可以成交。旧数据行中的历史 forward 字段不参与研究。',
        '只有信号日在所选区间、且收益结束日不晚于区间终点的信号期才纳入；交易日使用行情帧日期。未来缺价只减少收益配对样本，不改变当期因子有效样本或分层。',
        'Rank IC 为当期因子值与随后 H 日收益的 Spearman 秩相关，并列取平均秩；方向调整后 IC = 预设方向 × 原始 IC。ICIR = 各期 IC 均值 / 样本标准差，不年化；正 IC 期占比不是投资收益胜率。',
        'HAC 使用 Bartlett 权重 Newey–West 均值标准误，方差为 [Σu² + 2Σ_l(1−l/(L+1))Σ_grid距l u_t u_s] / n² × n/(n−1)。保留原始周度信号格间距；L 不低于收益重叠需要及自动带宽。缺失 IC 不压缩为连续观测。95% 区间和 p 值为正态近似，少于 ' + o.minPeriods + ' 个有效期或退化方差只作描述。',
        '五分位先按全部当期有效因子值及预设方向分组，再核对未来收益；按平均秩的百分位分箱，同值不拆组，空分位不补造。各期层内等权，跨期均值等权；Q5−Q1 和 Q5 相对同一期有效因子池的收益差是 H 日平均差，不拼接重叠收益净值。',
        o.controls.length ? '截面控制：对因子值以截距及所选正值控制变量的对数作 OLS，使用残差做 Rank IC；缺控制变量另计覆盖损失。它不是完整行业中性化，也不使用未来收益拟合。' : '默认不做中性化，直接研究原始因子的横截面排序；控制变量处理需用户显式选择。',
        '训练期要求收益结束日不晚于分界日，验证期要求信号日晚于分界日，跨界标签剔除。事后选择分界和参数仍是探索研究，方向不根据验证期自动翻转。'
      ];
      result.warnings = [];
      if (!periods.length) result.warnings.push('所选时间区间没有完整收益标签的信号期，请扩大区间或缩短持有期限。');
      if (result.summary.descriptive) result.warnings.push('有效期数不足或方差退化；当前统计仅作描述，不据此确认因子有效。');
      if (finite(result.coverage.labelCoverage) && result.coverage.labelCoverage < 1) result.warnings.push('未来价格标签不完整；配对 IC 和收益存在缺失选择风险，请同时检查覆盖率。');
      if (result.coverage.entryNotTradeableN) result.warnings.push('部分执行日价格虽可观察但无正成交量；这里是价格研究，不代表真实可成交业绩。');
      if (missingExecutionPeriods) result.warnings.push(missingExecutionPeriods + ' 个信号期的执行日不在行情日期中，未替换成未来其他日期。');
      if (o.controls.length) result.warnings.push('发行规模是发行时规模代理，不代表历史剩余余额；控制变量缺失会减少有效因子样本。');
      if (periods.some(function (p) { return p.factorN && p.quantiles.some(function (q) { return !q.signalN; }); })) result.warnings.push('部分期因子并列值较多，五分位存在空组；同值未被任意拆开。');
      result.version = VERSION; return result;
    }
    function compare(keys, options, progress) {
      keys = keys.filter(function (k, i, a) { return a.indexOf(k) === i; });
      var rows = keys.map(function (key, i) {
        var opts = Object.assign({}, options || {}, { key: key });
        if (opts.directions && (opts.directions[key] === -1 || opts.directions[key] === 1)) opts.direction = opts.directions[key];
        var a = analyze(opts), row = Object.assign({ key: key, name: (fieldMeta[key] || {}).n || key, direction: a.options.direction }, a.summary, { coverage: a.coverage, summary: a.summary });
        if (progress && typeof progress.onProgress === 'function') progress.onProgress({ completed: i + 1, total: keys.length, key: key });
        return row;
      });
      var qs = bh(rows.map(function (r) { return r.pValue; })); rows.forEach(function (r, i) { r.bhQ = qs[i]; });
      return { rows: rows, version: VERSION, method: ['因子均使用相同区间、收益期限和研究口径；不同字段的覆盖率可能不同，应与 IC 同时比较。', 'BH q 值仅对本次选中且可计算近似 p 值的因子集合做 Benjamini–Hochberg 调整；p 使用 HAC t 的双侧正态近似。'], warnings: ['因子相关、反复选择日期和参数、先看结果后选因子仍会产生多重试验偏差；q 值不代表因子已经通过独立样本验证。'] };
    }
    function correlations(keys, options) {
      keys = keys.filter(function (k, i, a) { return a.indexOf(k) === i; });
      if (keys.length > 12) throw Error('相关性比较最多选择 12 个因子');
      var o = normalize(options), sums = keys.map(function () { return keys.map(function () { return 0; }); }), counts = keys.map(function () { return keys.map(function () { return 0; }); }), sampleSums = keys.map(function () { return keys.map(function () { return 0; }); });
      weeks.forEach(function (w) {
        if (w.d < o.start || w.d > o.end) return;
        var rows = eligibleRows(w, o), vals = keys.map(function (key) { return factorValues(w, rows, Object.assign({}, o, { key: key })).values; });
        for (var i = 0; i < keys.length; i++) for (var j = i; j < keys.length; j++) {
          var r = spearman(vals[i], vals[j], o.minPairs); if (r == null) continue;
          var n = vals[i].filter(function (x, k) { return finite(x) && finite(vals[j][k]); }).length;
          sums[i][j] += r; counts[i][j]++; sampleSums[i][j] += n;
          if (i !== j) { sums[j][i] += r; counts[j][i]++; sampleSums[j][i] += n; }
        }
      });
      return { keys: keys, matrix: sums.map(function (row, i) { return row.map(function (v, j) { return counts[i][j] ? v / counts[i][j] : null; }); }), counts: counts,
        sampleCounts: sampleSums.map(function (row, i) { return row.map(function (v, j) { return counts[i][j] ? v / counts[i][j] : null; }); }), version: VERSION,
        method: ['对所选信号日期内各期做因子两两截面 Spearman 秩相关，然后按期等权平均；仅使用当期因子，不要求未来标签。方向保持原始因子口径，控制变量选项与主研究一致。'], warnings: ['不同因子对的缺失模式可能不同；这种按对取均值的矩阵不保证半正定，不能直接当作组合优化协方差矩阵。'] };
    }
    return { analyze: analyze, compare: compare, correlations: correlations, version: VERSION };
  }
  // A working-set projection, not a new dataset or a new signal calendar. Keep
  // every original week slot (HAC grid distances) and every market frame (label
  // endpoints, held off-pool securities and settlement) exactly as supplied.
  function createPartitionCache(data, limit) {
    var cache = new Map(), fields = data.fields || [];
    limit = Math.max(1, Math.min(8, limit || 3));
    return { select: function (selection) {
      var s = selection || {}, start = s.start || (data.period || [])[0] || '', end = s.end || (data.period || [])[1] || '';
      if (start > end) throw Error('研究分区的开始日不能晚于结束日');
      var keys = Array.from(new Set(s.keys || [])).sort(), families = s.families || [];
      fields.forEach(function (f) { if (families.indexOf(f.family || f.c) >= 0 && keys.indexOf(f.k) < 0) keys.push(f.k); });
      keys.sort();
      var groups = s.groups == null ? null : Array.from(new Set(s.groups)).sort();
      var signature = JSON.stringify([start, end, groups, keys]);
      if (cache.has(signature)) {
        var hit = cache.get(signature); cache.delete(signature); cache.set(signature, hit);
        return { data: hit.data, audit: Object.assign({}, hit.audit, { cache_hit: true }) };
      }
      var columns = []; fields.forEach(function (f, i) { if (keys.indexOf(f.k) >= 0) columns.push(i + 3); });
      var rows = 0, selectedWeeks = 0;
      var weeks = (data.weeks || []).map(function (w) {
        var selected = w.d >= start && w.d <= end;
        if (selected) selectedWeeks++;
        var projected = selected ? (w.rows || []).filter(function (r) { return groups == null || groups.indexOf(r[1]) >= 0; }).map(function (r) {
          var out = [r[0], r[1], r[2]];
          columns.forEach(function (i) { out[i] = r[i]; }); rows++; return out;
        }) : [];
        return Object.assign({}, w, { rows: projected });
      });
      var result = { data: Object.assign({}, data, { weeks: weeks }), audit: {
        schema: 'mf-working-set/1', storage: 'worker_memory_projection', source_data_version: (data.metadata || {}).data_version || null,
        start: start, end: end, keys: keys, groups: groups, selected_weeks: selectedWeeks, selected_rows: rows,
        total_week_slots: weeks.length, preserved_market_frames: ((data.market || {}).frames || []).length,
        signal_grid: 'original_slots', market_policy: 'full_original_frames', cache_hit: false
      } };
      cache.set(signature, result); while (cache.size > limit) cache.delete(cache.keys().next().value);
      return result;
    }, clear: function () { cache.clear(); }, size: function () { return cache.size; } };
  }
  // Compatibility transport only. Research formulas still consume the same
  // complete dataset; this path is used when a persistent Worker cannot run.
  async function preparePartitionedData(baseURL, options) {
    options = options || {};
    var expected = options.expected || {}, signal = options.signal, fetcher = options.fetch || globalThis.fetch;
    function fault(message, code) { var e = Error(message); e.code = code || 'MF_INTEGRITY'; return e; }
    function aborted() { if (signal && signal.aborted) { var e = Error('多因子分区加载已取消'); e.name = 'AbortError'; throw e; } }
    if (!globalThis.crypto || !globalThis.crypto.subtle) throw fault('当前页面无法校验 SHA-256，请通过 HTTPS 或本机服务打开，不会跳过完整性校验');
    if (typeof fetcher !== 'function' || typeof DecompressionStream !== 'function') throw fault('当前浏览器不支持已校验的研究分区加载，请使用近期 Chrome、Edge 或 Safari');
    async function hex(bytes) { return Array.from(new Uint8Array(await globalThis.crypto.subtle.digest('SHA-256', bytes))).map(function (b) { return b.toString(16).padStart(2, '0'); }).join(''); }
    function assetURL(path) {
      if (typeof path !== 'string' || !/^mf_partitions\/[a-f0-9]{20}\/[a-zA-Z0-9_.-]+\.json\.gz$/.test(path)) throw fault('研究分区路径无效');
      return new URL(path, baseURL).href;
    }
    async function asset(desc) {
      aborted();
      var response = await fetcher(assetURL(desc.path), { signal: signal });
      if (!response.ok) throw fault('研究分区加载失败：' + desc.path + '（HTTP ' + response.status + '）');
      var bytes = await response.arrayBuffer(), digest = await hex(bytes), raw;
      if (bytes.byteLength === desc.bytes && digest === desc.sha256) raw = await new Response(new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();
      else if (bytes.byteLength === desc.uncompressed_bytes && digest === desc.raw_sha256) raw = bytes; // Content-Encoding:gzip hosts.
      else throw fault('研究分区 SHA-256 或长度校验失败：' + desc.path);
      if (raw.byteLength !== desc.uncompressed_bytes || await hex(raw) !== desc.raw_sha256) throw fault('研究分区解压长度或 SHA-256 校验失败：' + desc.path);
      aborted(); return JSON.parse(new TextDecoder().decode(raw));
    }
    aborted();
    var response;
    try { response = await fetcher(new URL('mf_partitions/manifest.json', baseURL).href, { cache: 'no-cache', signal: signal }); }
    catch (e) { if (e.name === 'AbortError') throw e; throw fault('研究分区清单不可读取：' + e.message, expected.manifest_sha256 ? 'MF_INTEGRITY' : 'MF_PARTITIONS_UNAVAILABLE'); }
    if (response.status === 404) throw fault('研究分区清单缺失', expected.manifest_sha256 ? 'MF_INTEGRITY' : 'MF_PARTITIONS_UNAVAILABLE');
    if (!response.ok) throw fault('研究分区清单加载失败（HTTP ' + response.status + '）');
    var manifestBytes = await response.arrayBuffer(), manifestSHA = await hex(manifestBytes), m = JSON.parse(new TextDecoder().decode(manifestBytes));
    if (expected.manifest_sha256 && manifestSHA !== expected.manifest_sha256) throw fault('研究分区清单与当前页面构建不一致');
    if (!m || m.schema !== 'mf-partitioned/1' || !m.source || !/^[a-f0-9]{64}$/.test(m.source.sha256) || !Number.isInteger(m.source.uncompressed_bytes) || m.source.uncompressed_bytes <= 0 || !Array.isArray(m.fields) || !Array.isArray(m.market)) throw fault('研究分区清单无效');
    if ((expected.sha256 && expected.sha256 !== m.source.sha256) || (expected.uncompressed_bytes && expected.uncompressed_bytes !== m.source.uncompressed_bytes)) throw fault('研究分区与原整体数据身份不一致');
    var descriptors = [m.common].concat(m.fields, m.market), paths = new Set();
    descriptors.forEach(function (d) {
      if (!d || !Number.isInteger(d.bytes) || d.bytes <= 0 || d.bytes >= 24 * 1024 * 1024 || !Number.isInteger(d.uncompressed_bytes) || d.uncompressed_bytes <= 0 || !/^[a-f0-9]{64}$/.test(d.sha256) || !/^[a-f0-9]{64}$/.test(d.raw_sha256)) throw fault('研究分区缺少长度或 SHA-256');
      assetURL(d.path);
      if (!d.path.startsWith('mf_partitions/' + m.source.sha256.slice(0, 20) + '/') || paths.has(d.path)) throw fault('研究分区源身份或路径重复');
      paths.add(d.path);
    });
    var data = await asset(m.common);
    if (!data || ![2, 3].includes(data.v) || !data.metadata || data.metadata.data_version !== m.source.data_version || !Array.isArray(data.fields) || !Array.isArray(data.weeks) || !data.market || !Array.isArray(data.market.frames)) throw fault('研究分区基础数据格式或身份不兼容');
    var weeks = data.weeks, frames = data.market.frames, coverage = data.fields.map(function () { return new Uint8Array(weeks.length); }), marketCoverage = new Uint8Array(frames.length);
    weeks.forEach(function (w) { if (!Array.isArray(w.rows) || w.rows.some(function (r) { return !Array.isArray(r) || r.length !== 3; })) throw fault('研究分区基础行索引不完整'); });
    function indices(desc, records) {
      var ids = []; records.forEach(function (record, i) { if (record.d >= desc.start && record.d <= desc.end) ids.push(i); });
      if (typeof desc.start !== 'string' || typeof desc.end !== 'string' || !ids.length || ids.length !== desc.count) throw fault('研究分区日期范围或数量不完整');
      return ids;
    }
    var fieldIndices = m.fields.map(function (d) {
      if (!Array.isArray(d.columns) || !d.columns.length || !Array.isArray(d.keys) || d.keys.length !== d.columns.length || new Set(d.columns).size !== d.columns.length) throw fault('因子分区列身份不完整');
      var ids = indices(d, weeks);
      d.columns.forEach(function (col, j) {
        if (!Number.isInteger(col) || col < 3 || col >= data.fields.length + 3 || data.fields[col - 3].k !== d.keys[j]) throw fault('因子分区列身份不一致');
        ids.forEach(function (i) { if (coverage[col - 3][i]++) throw fault('因子分区日期或字段重复'); });
      }); return ids;
    });
    var marketIndices = m.market.map(function (d) { var ids = indices(d, frames); ids.forEach(function (i) { if (marketCoverage[i]++) throw fault('行情分区日期重复'); }); return ids; });
    if (coverage.some(function (c) { return c.some(function (n) { return n !== 1; }); }) || marketCoverage.some(function (n) { return n !== 1; })) throw fault('研究清单缺少完整日期或字段分区');
    var completed = 1;
    if (options.onProgress) options.onProgress({ completed: completed, total: descriptors.length });
    // Serial reads bound transient buffers and preserve every original row slot.
    for (var n = 0; n < m.fields.length; n++) {
      var desc = m.fields[n], part = await asset(desc), wanted = new Set(fieldIndices[n]);
      if (part.schema !== 'mf-field-block/1' || JSON.stringify(part.columns) !== JSON.stringify(desc.columns) || JSON.stringify(part.keys) !== JSON.stringify(desc.keys) || !Array.isArray(part.weeks) || part.weeks.length !== wanted.size) throw fault('因子分区列或日期身份不一致');
      part.weeks.forEach(function (pair) {
        if (!Array.isArray(pair) || !wanted.delete(pair[0]) || !Array.isArray(pair[1]) || pair[1].length !== weeks[pair[0]].rows.length) throw fault('因子分区行或日期索引不一致');
        pair[1].forEach(function (row, r) { if (!Array.isArray(row) || row.length !== part.columns.length) throw fault('因子分区列数不一致'); part.columns.forEach(function (col, j) { weeks[pair[0]].rows[r][col] = row[j]; }); });
      });
      if (options.onProgress) options.onProgress({ completed: ++completed, total: descriptors.length });
    }
    for (var f = 0; f < m.market.length; f++) {
      var marketDesc = m.market[f], block = await asset(marketDesc), frameIds = new Set(marketIndices[f]);
      if (block.schema !== 'mf-market-block/1' || !Array.isArray(block.frames) || block.frames.length !== frameIds.size) throw fault('行情分区日期不完整');
      block.frames.forEach(function (pair) { if (!Array.isArray(pair) || !frameIds.delete(pair[0]) || !pair[1] || pair[1].d !== frames[pair[0]].d) throw fault('行情分区日期索引不一致'); frames[pair[0]] = pair[1]; });
      if (options.onProgress) options.onProgress({ completed: ++completed, total: descriptors.length });
    }
    aborted(); delete data._ui_preview;
    return { data: data, source: Object.assign({ mode: 'partitioned', manifest_sha256: manifestSHA }, m.source), audit: { schema: 'mf-full-partition-loader/1', backend: 'main_thread', loaded_assets: descriptors.length, manifest_sha256: manifestSHA, source_sha256: m.source.sha256, source_uncompressed_bytes: m.source.uncompressed_bytes, integrity: 'all_partition_sha256_and_lengths_verified; source_identity_from_verified_export' } };
  }
  return { create: create, createPartitionCache: createPartitionCache, preparePartitionedData: preparePartitionedData,
    partitionTransport: { schema: 'mf-partitioned/1', full_main_thread: 'mf-full-partition-loader/1' }, version: VERSION,
    _test: { rankAvg: rankAvg, spearman: spearman, hacSummary: hacSummary, residualize: residualize, quantileMembership: quantileMembership, BH: bh, normalP: normalP } };
});
