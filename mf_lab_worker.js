/* Persistent MF compute owner. No DOM rendering, no alternate research math. */
'use strict';
self.window=self;
var buildQuery=new URL(self.location.href).searchParams.get('build');
importScripts('mf_research_engine.js'+(buildQuery?'?build='+encodeURIComponent(buildQuery):''),'mf_lab_app.js'+(buildQuery?'?build='+encodeURIComponent(buildQuery):''));
var dataset=null,partitions=null,manifest=null,sourceIdentity=null,loaded=new Map(),tail=Promise.resolve();
function fault(message,code){var e=Error(message);e.code=code||'MF_WORKER_ERROR';return e;}
function hex(bytes){return crypto.subtle.digest('SHA-256',bytes).then(function(hash){return Array.from(new Uint8Array(hash)).map(function(b){return b.toString(16).padStart(2,'0');}).join('');});}
function assetPath(path){
  if(typeof path!=='string'||!/^mf_partitions\/[a-f0-9]{20}\/[a-zA-Z0-9_.-]+\.json\.gz$/.test(path))throw fault('研究分区路径无效');
  return new URL(path,self.location.href).href;
}
async function fetchAsset(desc){
  if(typeof crypto==='undefined'||!crypto.subtle)throw fault('当前页面无法校验 SHA-256，请通过 HTTPS 或本机服务打开，不会跳过完整性校验','MF_INTEGRITY');
  if(!desc||!Number.isInteger(desc.bytes)||desc.bytes<=0||desc.bytes>=24*1024*1024||!Number.isInteger(desc.uncompressed_bytes)||desc.uncompressed_bytes<=0||!/^[a-f0-9]{64}$/.test(desc.sha256)||!/^[a-f0-9]{64}$/.test(desc.raw_sha256))throw fault('研究分区缺少长度或 SHA-256');
  var response=await fetch(assetPath(desc.path));if(!response.ok)throw fault('研究分区加载失败：'+desc.path+'（HTTP '+response.status+'）');
  var buffer=await response.arrayBuffer(),hash=await hex(buffer),raw;
  if(buffer.byteLength===desc.bytes&&hash===desc.sha256){
    raw=await new Response(new Blob([buffer]).stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();
  }else if(buffer.byteLength===desc.uncompressed_bytes&&hash===desc.raw_sha256){
    // A host may send Content-Encoding:gzip, which fetch transparently decodes.
    raw=buffer;
  }else throw fault('研究分区 SHA-256 校验失败：'+desc.path,'MF_INTEGRITY');
  if(raw.byteLength!==desc.uncompressed_bytes||await hex(raw)!==desc.raw_sha256)throw fault('研究分区解压长度或 SHA-256 校验失败：'+desc.path,'MF_INTEGRITY');
  return JSON.parse(new TextDecoder().decode(raw));
}
function validateDataset(data){if(!data||![2,3].includes(data.v)||!data.market||!data.metadata||!Array.isArray(data.weeks)||!Array.isArray(data.fields))throw fault('多因子数据格式不兼容');}
async function initPartitioned(expected){
  var response;
  try{response=await fetch(new URL('mf_partitions/manifest.json',self.location.href).href,{cache:'no-cache'});}
  catch(e){throw fault('研究分区清单不可读取：'+e.message,'MF_PARTITIONS_UNAVAILABLE');}
  if(response.status===404)throw fault(expected&&expected.manifest_sha256?'当前构建声明的研究分区清单缺失；请重新发布完整文件':'尚未提供研究分区清单',expected&&expected.manifest_sha256?'MF_INTEGRITY':'MF_PARTITIONS_UNAVAILABLE');
  if(!response.ok)throw fault('研究分区清单加载失败（HTTP '+response.status+'）');
  var manifestBytes=await response.arrayBuffer(),manifestSHA=await hex(manifestBytes);
  if(expected&&expected.manifest_sha256&&manifestSHA!==expected.manifest_sha256)throw fault('研究分区清单与当前页面构建不一致，请刷新完整站点后重试','MF_INTEGRITY');
  var m=JSON.parse(new TextDecoder().decode(manifestBytes));
  if(!m||m.schema!=='mf-partitioned/1'||!m.source||!/^[a-f0-9]{64}$/.test(m.source.sha256)||!Number.isInteger(m.source.uncompressed_bytes)||m.source.uncompressed_bytes<=0||!Array.isArray(m.fields)||!Array.isArray(m.market))throw fault('研究分区清单无效','MF_INTEGRITY');
  if(expected&&expected.sha256&&m.source.sha256!==expected.sha256)throw fault('研究数据版本已变化；请重新打开研究页，旧配置与结果保留','MF_INTEGRITY');
  var data=await fetchAsset(m.common);validateDataset(data);
  if(data.metadata.data_version!==m.source.data_version)throw fault('研究分区数据身份不一致','MF_INTEGRITY');
  var all=[m.common].concat(m.fields,m.market),paths=new Set();
  all.forEach(function(d){assetPath(d.path);if(!d.path.startsWith('mf_partitions/'+m.source.sha256.slice(0,20)+'/'))throw fault('研究分区与原整体身份不一致','MF_INTEGRITY');if(paths.has(d.path))throw fault('研究分区清单含重复路径','MF_INTEGRITY');paths.add(d.path);});
  manifest=m;dataset=data;sourceIdentity=m.source;partitions=MFResearch.createPartitionCache(dataset);loaded.clear();loaded.set(m.common.path,true);
  return {summary:MFLabCompute.summary(dataset),source:{mode:'partitioned',sha256:m.source.sha256,manifest_sha256:manifestSHA},audit:{mode:'partitioned',loaded_assets:1,source_sha256:m.source.sha256,manifest_sha256:manifestSHA}};
}
async function initPacked(message){
  var header=message.header,chunks=message.chunks;
  if(message.reload){
    var expected=message.reload;
    importScripts(new URL(expected.schema==='mf-parts/1'?'multifactor_lab_data.p1.js':'multifactor_lab_data.js',self.location.href).href+'?v='+expected.sha256);
    var raw=expected.schema==='mf-parts/1'?self.MF_LAB_DATA_PARTS:self.MF_LAB_DATA_PACKED;
    MFLabCompute.validateHeader(raw,expected.schema);
    if(raw.sha256!==expected.sha256)throw fault('研究数据版本已变化；请重新打开研究页','MF_INTEGRITY');
    if(expected.schema==='mf-parts/1')for(var n=2;n<=raw.total;n++)importScripts(new URL('multifactor_lab_data.p'+n+'.js',self.location.href).href+'?v='+expected.sha256);
    header=raw;chunks=raw.parts||[raw.data];
  }
  MFLabCompute.validateHeader(Object.assign({},header,{parts:chunks}),header.schema);
  if(header.schema==='mf-parts/1'&&chunks.length!==header.total)throw fault('原始研究分片不完整','MF_INTEGRITY');
  var data=await MFLabCompute.decode(chunks,header);validateDataset(data);
  delete self.MF_LAB_DATA_PARTS;delete self.MF_LAB_DATA_PACKED;
  dataset=data;manifest=null;partitions=MFResearch.createPartitionCache(data);loaded.clear();sourceIdentity={sha256:header.sha256};
  return {summary:MFLabCompute.summary(dataset),source:{mode:'packed',schema:header.schema,sha256:header.sha256,total:header.total},audit:{mode:'packed',source_sha256:header.sha256}};
}
function dependencies(keys,config){
  var built=new Set(dataset.fields.map(function(f){return f.k;})),defs={},seen=new Set(),out=new Set();
  (config.custom||[]).forEach(function(c){defs[c.key]=c;});
  function add(key){
    if(built.has(key)){out.add(key);return;}if(key==='__score'){Object.keys(config.sel||{}).forEach(function(g){config.sel[g].forEach(function(p){add(p.k);});});return;}
    if(seen.has(key))return;seen.add(key);
    var c=defs[key];if(!c)throw fault('研究字段或自定义依赖缺失：'+key);
    (c.expr.match(/[A-Za-z_][A-Za-z0-9_]*/g)||[]).forEach(function(dep){if(!/^(log|abs|sqrt|neg|min|max|pow)$/.test(dep))add(dep);});
  }
  keys.forEach(add);return Array.from(out).sort();
}
async function ensureSelection(selection){
  if(!manifest)return [];
  var signalDates=dataset.weeks.filter(function(w){return w.d>=selection.start&&w.d<=selection.end;}).map(function(w){return w.d;});
  selection.keys.forEach(function(key){var blocks=manifest.fields.filter(function(d){return d.keys.indexOf(key)>=0;});
    if(signalDates.some(function(date){return !blocks.some(function(d){return d.start<=date&&d.end>=date;});}))throw fault('研究清单缺少所选字段的完整日期分区：'+key,'MF_INTEGRITY');
  });
  if(dataset.market.frames.some(function(f){return f.d>=selection.start&&f.d<=selection.end&&!manifest.market.some(function(d){return d.start<=f.d&&d.end>=f.d;});}))throw fault('研究清单缺少所选日期的行情分区','MF_INTEGRITY');
  var wanted=manifest.fields.filter(function(d){return d.end>=selection.start&&d.start<=selection.end&&d.keys.some(function(k){return selection.keys.indexOf(k)>=0;});})
    .concat(manifest.market.filter(function(d){return d.end>=selection.start&&d.start<=selection.end;}));
  var fetched=[];
  // Serial acquisition bounds transient decompressed memory and gives failures
  // an exact asset. Completed immutable assets remain reusable on a retry.
  for(var i=0;i<wanted.length;i++){
    var desc=wanted[i];if(loaded.has(desc.path))continue;
    var part=await fetchAsset(desc);
    if(part.schema==='mf-field-block/1'){
      if(JSON.stringify(part.columns)!==JSON.stringify(desc.columns)||JSON.stringify(part.keys)!==JSON.stringify(desc.keys))throw fault('因子分区列身份不一致','MF_INTEGRITY');
      var weekIds=new Set(),expectedWeeks=dataset.weeks.filter(function(w){return w.d>=desc.start&&w.d<=desc.end;}).length;
      if(part.weeks.length!==desc.count||part.weeks.length!==expectedWeeks)throw fault('因子分区信号日期不完整','MF_INTEGRITY');
      part.weeks.forEach(function(pair){
        if(weekIds.has(pair[0]))throw fault('因子分区信号日期重复','MF_INTEGRITY');weekIds.add(pair[0]);
        var w=dataset.weeks[pair[0]];if(!w||w.d<desc.start||w.d>desc.end||pair[1].length!==w.rows.length)throw fault('因子分区日期或行索引不一致','MF_INTEGRITY');
        pair[1].forEach(function(values,r){if(values.length!==part.columns.length)throw fault('因子分区列数不一致','MF_INTEGRITY');part.columns.forEach(function(col,j){w.rows[r][col]=values[j];});});
      });
    }else if(part.schema==='mf-market-block/1'){
      var frameIds=new Set(),expectedFrames=dataset.market.frames.filter(function(f){return f.d>=desc.start&&f.d<=desc.end;}).length;
      if(part.frames.length!==desc.count||part.frames.length!==expectedFrames)throw fault('行情分区日期不完整','MF_INTEGRITY');
      part.frames.forEach(function(pair){if(frameIds.has(pair[0]))throw fault('行情分区日期重复','MF_INTEGRITY');frameIds.add(pair[0]);var old=dataset.market.frames[pair[0]],frame=pair[1];if(!old||old.d!==frame.d||frame.d<desc.start||frame.d>desc.end)throw fault('行情分区日期索引不一致','MF_INTEGRITY');dataset.market.frames[pair[0]]=frame;});
    }else throw fault('研究分区类型不支持','MF_INTEGRITY');
    loaded.set(desc.path,true);fetched.push(desc.path);
  }
  return fetched;
}
async function compute(message){
  if(!dataset)throw fault('研究数据尚未初始化');
  var config=message.config,options=message.options||{},keys=message.keys||[options.key],backtest=message.method==='backtest';
  if(!config||!config.params||!config.sel||!Array.isArray(config.custom))throw fault('研究组合配置不完整');
  if(backtest)keys=Object.keys(config.sel).flatMap(function(g){return config.sel[g].map(function(p){return p.k;});});
  var range=backtest?[config.params.start||dataset.period[0],config.params.end||dataset.period[1]]:[options.start||dataset.period[0],options.end||dataset.period[1]];
  var groups=backtest?(config.params.mode==='combo'?null:[Number(config.params.mode)]):(options.group==='all'||options.group==null?null:[Number(options.group)]);
  var controls=options.controls==='price_parity_size'?['price','cb_value','issue_size_yi']:options.controls||[];
  var selection={start:range[0],end:range[1],groups:groups,keys:dependencies(keys.concat(controls),config)};
  var fetched=await ensureSelection(selection),working=partitions.select(selection);
  MFLabCompute.configure(working.data,config);
  var result;
  if(backtest){result=MFLabCompute.runBacktest();if(message.strategy)result.strategy=message.strategy;result=MFLabCompute.snapshot(result).result;}
  else{
    var engine=MFResearch.create(working.data,{valueGetter:function(row,key){return MFLabCompute.rowFactor(row,key);},scoreGetter:MFLabCompute.scoreGroup});
    if(message.method==='analyze')result=engine.analyze(options);
    else if(message.method==='compare')result=engine.compare(keys,options);
    else if(message.method==='correlations')result=engine.correlations(keys,options);
    else throw fault('未知研究任务');
  }
  return {result:result,audit:Object.assign({},working.audit,{transport:manifest?'partitioned':'packed',source_sha256:sourceIdentity.sha256,
    fetched_assets:fetched,cached_assets:loaded.size,market_policy:manifest?'original_day_axis; selected_interval_quotes_verified':'full_original_frames',
    source_integrity:manifest?manifest.integrity:'original_payload_sha256_verified'})};
}
self.onmessage=function(event){
  var message=event.data;
  tail=tail.catch(function(){}).then(async function(){
    try{
      var result=message.type==='hello'?{protocol:'mf-compute/1'}:message.type==='initPartitioned'?await initPartitioned(message.expected):message.type==='initPacked'?await initPacked(message):message.type==='compute'?await compute(message):null;
      if(!result)throw fault('未知多因子 Worker 请求');self.postMessage({id:message.id,ok:true,value:result});
    }catch(e){self.postMessage({id:message.id,ok:false,error:e.message||String(e),code:e.code||'MF_WORKER_ERROR'});}
  });
};
