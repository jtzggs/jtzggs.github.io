/* Independent trial-ledger storage. Loading research or its UI is not required. */
(function (root) {
  'use strict';
  if (root.ResearchTrialLedger) {
    if (typeof module !== 'undefined' && module.exports) module.exports = root.ResearchTrialLedger;
    return;
  }
  const KEY = 'mf_factor_research_trials_v1', SCHEMA = 'factor-research-trials/1.0';
  const RESTORE = 'cb-research-restore-journal-v1';
  const statuses = ['running', 'completed', 'completed_stale', 'failed', 'blocked', 'superseded'];
  const object = x => x && typeof x === 'object' && !Array.isArray(x);
  const clone = x => JSON.parse(JSON.stringify(x));
  function stable(x) {
    if (Array.isArray(x)) return '[' + x.map(stable).join(',') + ']';
    if (object(x)) return '{' + Object.keys(x).sort().map(k => JSON.stringify(k) + ':' + stable(x[k])).join(',') + '}';
    return JSON.stringify(x);
  }
  const date = x => typeof x === 'string' && /^\d{4}-\d{2}-\d{2}T(?:[01]\d|2[0-3]):[0-5]\d:[0-5]\d(?:\.\d+)?(?:Z|[+-](?:[01]\d|2[0-3]):[0-5]\d)$/.test(x) &&
    Number.isFinite(Date.parse(x)) && new Date(x.slice(0, 10) + 'T00:00:00Z').toISOString().slice(0, 10) === x.slice(0, 10);
  function jsonValue(x) {
    if (x === null || typeof x === 'string' || typeof x === 'boolean') return;
    if (typeof x === 'number' && Number.isFinite(x)) return;
    if (Array.isArray(x)) { for (let i = 0; i < x.length; i++) jsonValue(x[i]); return; }
    if (object(x) && Object.prototype.toString.call(x) === '[object Object]') { Object.values(x).forEach(jsonValue); return; }
    throw Error('试验记录含非 JSON 值或非有限数值');
  }
  function validateRecord(r) {
    jsonValue(r);
    if (!object(r) || typeof r.id !== 'string' || !r.id.trim() || !date(r.started_at) ||
        (r.updated_at != null && (!date(r.updated_at) || Date.parse(r.updated_at) < Date.parse(r.started_at))) ||
        (r.finished_at != null && !date(r.finished_at)) || !statuses.includes(r.status)) throw Error('试验成员缺少有效 ID、开始时间或状态');
    if (r.adoption != null && !['not_adopted', 'added_to_strategy'].includes(r.adoption)) throw Error('试验采纳状态无效：' + r.id);
    if (r.retention_events != null && (!Array.isArray(r.retention_events) || r.retention_events.some(e => !object(e) || typeof e.kind !== 'string' || !date(e.at)))) throw Error('试验保留记录无效：' + r.id);
    if (r.capture != null) {
      const c = r.capture;
      if (!object(c) || !['single', 'comparison', 'correlation'].includes(c.kind) || !object(c.options) ||
          !Array.isArray(c.keys) || c.keys.some(k => typeof k !== 'string' || !k) || new Set(c.keys).size !== c.keys.length ||
          !object(c.directions) || c.keys.some(k => c.directions[k] !== 1 && c.directions[k] !== -1) || Object.values(c.directions).some(d => d !== 1 && d !== -1) ||
          !Array.isArray(c.factor_definitions) || c.factor_definitions.some(f => !object(f) || typeof f.k !== 'string') ||
          !object(c.metadata) || !object(c.data_identity) || !object(c.fingerprints)) throw Error('冻结试验条件或身份不完整：' + r.id);
    }
    // Early ledgers can lack a capture. Preserve those records as old,
    // unauthenticated history; restoration never fills in missing evidence.
    return clone(r);
  }
  function validate(value) {
    if (!object(value) || value.schema_version !== SCHEMA || !Array.isArray(value.records)) throw Error('不是支持的因子研究试验台账');
    const records = value.records.map(validateRecord);
    return merge([], records);
  }
  function identity(r) { const x = clone(r); delete x.restoration; return stable(x); }
  function merge(previous, current, mutableSession) {
    const byId = new Map();
    previous.concat(current).forEach(r => {
      const old = byId.get(r.id);
      if (!old) byId.set(r.id, clone(r));
      else if (identity(old) !== identity(r)) {
        const owned = mutableSession && old.session_id === mutableSession && r.session_id === mutableSession && stable(old.capture) === stable(r.capture);
        if (!owned) throw Error('试验 ID 冲突，未覆盖任何记录：' + r.id);
        if ((r.updated_at || r.started_at) >= (old.updated_at || old.started_at)) byId.set(r.id, clone(r));
      }
    });
    return [...byId.values()].sort((a, b) => a.started_at.localeCompare(b.started_at) || a.id.localeCompare(b.id));
  }
  function read() {
    let raw = null;
    try {
      raw = localStorage.getItem(KEY);
      return {raw, records: raw == null ? [] : validate(JSON.parse(raw)), error: null};
    } catch (e) { return {raw, records: [], error: '已有试验台账损坏或不可读取，原值保留：' + e.message}; }
  }
  function restoreRaw(raw) {
    if (raw == null) {
      if (typeof localStorage.removeItem !== 'function') throw Error('存储不支持恢复原空值');
      localStorage.removeItem(KEY);
    } else localStorage.setItem(KEY, raw);
    if (localStorage.getItem(KEY) !== raw) throw Error('恢复后核验不一致');
  }
  function write(records, beforeRaw) {
    if (localStorage.getItem(KEY) !== beforeRaw) throw Error('台账已被另一页面更新，请重新校验后导入');
    const serialized = JSON.stringify({schema_version: SCHEMA, records});
    try {
      localStorage.setItem(KEY, serialized);
      if (localStorage.getItem(KEY) !== serialized) throw Error('台账写入后核验不一致');
    } catch (e) {
      if (localStorage.getItem(KEY) !== beforeRaw) {
        try { restoreRaw(beforeRaw); } catch (rollback) { throw Error('台账写入失败且恢复受阻，请保留导入文件和原始台账：' + e.message + '；' + rollback.message); }
      }
      throw Error('台账未保存，旧数据保留；可导出记录后重试：' + e.message);
    }
  }
  function persist(records, mutableSession) {
    if (localStorage.getItem(RESTORE)) throw Error('存在未完成导入的恢复日志，请先恢复；本次试验保留在内存，可导出');
    const existing = read();
    if (existing.error) throw Error(existing.error);
    const merged = merge(existing.records, records.map(validateRecord), mutableSession);
    write(merged, existing.raw);
    return merged;
  }
  function prepare(value, extraRecords, mutableSession) {
    const incoming = validate(value), existing = read();
    if (existing.error) throw Error(existing.error);
    const current = merge(existing.records, (extraRecords || []).map(validateRecord), mutableSession);
    const merged = merge(current, incoming), oldIds = new Set(current.map(r => r.id));
    const source = {schema_version: value.schema_version, exported_at: value.exported_at || null, source_storage: value.storage || null};
    merged.forEach(r => {
      if (!oldIds.has(r.id)) r.restoration = {source: clone(source), source_status: r.status,
        previous_restoration: clone(r.restoration || null),
        verification: 'not_authenticated', grants_validation: false, strict_pit_certified: false};
    });
    return {beforeRaw: existing.raw, records: merged, imported: incoming.filter(r => !oldIds.has(r.id)).length,
      duplicates: incoming.filter(r => oldIds.has(r.id)).length};
  }
  function importLedger(value, extraRecords, mutableSession) {
    if (localStorage.getItem(RESTORE)) throw Error('存在未完成导入的恢复日志，请先恢复；旧台账未覆盖');
    const plan = prepare(value, extraRecords, mutableSession); write(plan.records, plan.beforeRaw);
    return {imported: plan.imported, duplicates: plan.duplicates, total: plan.records.length, verification: 'not_authenticated'};
  }
  function snapshot(extraRecords, mutableSession) {
    const existing = read(); let records = (extraRecords || []).map(validateRecord), error = existing.error;
    if (!error) {
      try { records = merge(existing.records, records, mutableSession); } catch (e) { error = e.message; }
    }
    return clone({schema_version: SCHEMA, exported_at: new Date().toISOString(), records,
      storage: {backend: 'localStorage', key: KEY, status: error ? 'error' : 'saved', error,
        unreadable_existing: error ? existing.raw : null},
      limitations: ['导入仅校验格式与 ID 一致性，保留来源及旧状态，不授予认证、样本外或 strict PIT 验证。',
        '台账仅覆盖本地已记录尝试，不能证明完整历史；BH 校正仍仅限当次比较集合。']});
  }
  const api = {key: KEY, schema: SCHEMA, stable, validate, merge, read, persist, prepare, write, restoreRaw, snapshot, importLedger};
  root.ResearchTrialLedger = api;
  root.importResearchTrialLedger = value => importLedger(value);
  root.researchTrialLedgerSnapshot = () => snapshot();
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(typeof window !== 'undefined' ? window : globalThis);
