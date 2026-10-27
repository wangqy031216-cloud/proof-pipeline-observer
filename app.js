/* Pure transformations of recorded tool events. No synthetic solver actions. */
(function (root, factory) {
  const api = factory();
  if (typeof window === 'object') window.ProofTrace = api;
  if (typeof module === 'object' && module.exports) module.exports = api;
  else root.ProofTrace = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';
  const stages = [
    {id:'context',label:'读证明'}, {id:'plan',label:'拆 DAG'}, {id:'statement',label:'转译节点'},
    {id:'search',label:'检索'}, {id:'prove',label:'证明'}, {id:'memory',label:'存事实／经验'},
    {id:'compression',label:'压缩上下文'}, {id:'verify',label:'验收'}
  ];
  const labels = {get_context:'读取证明上下文',set_plan:'规划证明依赖',add_node:'新增辅助命题',review_node:'审核已有节点声明',check_route:'检查节点声明与路线',search_library:'检索证明库',inspect_library:'查看库中声明',probe_proof:'局部 Lean 检查',attempt_proof:'提交根证明',check_node:'检查辅助引理',finalize:'最终验收',report_failure:'报告转译未完成',request_compaction:'主动申请压缩',prepare_compaction:'压缩前整理经验'};
  const stageOf = tool => ({get_context:'context',set_plan:'plan',add_node:'plan',review_node:'statement',check_route:'statement',search_library:'search',inspect_library:'search',probe_proof:'prove',attempt_proof:'prove',check_node:'prove',save_experience:'memory',request_compaction:'compression',prepare_compaction:'memory',finalize:'verify',report_failure:'verify',replay:'verify'})[tool] || 'context';
  function time(value) { const n=typeof value==='number' ? (value<1e11?value*1000:value) : Date.parse(value);return Number.isFinite(n)?n:null; }
  function chronological(previous, incoming) {
    const map=new Map(previous.map(e=>[String(e.seq),e]));
    (incoming||[]).forEach(e=>{if(e&&e.seq!=null)map.set(String(e.seq),e);});
    return [...map.values()].sort((a,b)=>{const x=time(a.at),y=time(b.at);return x!=null&&y!=null ? x-y||Number(a.seq)-Number(b.seq):Number(a.seq)-Number(b.seq);});
  }
  function isTool(e) { return String(e._source_key||'').startsWith('tool:') && !!e.details?.tool; }
  function isSnapshot(e) { return e.details?.timestamp_kind==='observer_received'; }
  function proofIndices(events) {
    const times=events.filter(e=>isTool(e)||e.scope==='proof'&&!isSnapshot(e)&&!String(e.kind).startsWith('statement.')).map(e=>time(e.at)).filter(t=>t!=null);
    const start=times.length?Math.min(...times):null;
    return events.flatMap((e,i)=>{
      if(e.scope==='main'||e.statement_context_id==='main'||String(e._source_key||'').startsWith('statement:')&&!String(e._source_key).startsWith('statement:helper:'))return [];
      if(isTool(e)||e.scope==='proof'&&!isSnapshot(e)||String(e._source_key||'').startsWith('statement:helper:')||String(e._source_key||'').startsWith('compression:'))return [i];
      if(isSnapshot(e)&&(e.proof_started===true||start!=null&&time(e.at)>=start))return [i];
      return [];
    });
  }
  function statusOf(tool,result) {
    if(result?.kind==='infrastructure_error'||result?.kind==='infrastructure_blocked')return 'infrastructure_error';
    if(tool==='get_context'&&result?.ok==null)return 'returned';
    if(result?.ok===true){
      if(tool==='request_compaction'||tool==='prepare_compaction')return 'recorded';
    if(tool==='save_experience')return result.already_saved===true?'checked':'recorded';
      if(tool==='set_plan')return 'planned';if(tool==='add_node')return 'recorded';
      if(tool==='report_failure')return 'translation_failed';
      if(tool==='probe_proof')return result.open_goal_count===0?'closed':'progress';
      if(tool==='review_node')return 'accepted';
      if(['get_context','search_library','inspect_library','check_route'].includes(tool))return 'checked';
      return 'passed';
    }
    if(result?.ok===false)return 'tool_rejected';
    return 'unknown';
  }
  function summaryOf(tool,args,result,done) {
    const node=args.target_id||args.node_id||args.node?.id||'root';
    if(!done)return tool==='review_node'?'等待该节点的声明转译 / 审核返回':'等待原工具调用返回';
    if(tool==='get_context'&&result?.ok!==false){
      const mode=result?.context_update===true?'增量读取当前证明状态':result?.context_update===false?'全量读取证明上下文':'读取证明上下文（原记录未标明全量或增量）';
      const target=result?.current_node?.id;
      return mode+(target?'；当前目标：'+target:'')+(result?.context_update===true?'；未变内容沿用上次快照':'');
    }
    if(result?.ok!==true)return String(result?.diagnostics||result?.reason||result?.kind||'原记录未给出检查通过结果').slice(0,220);
    if(tool==='request_compaction')return (result.already_requested?'已有压缩申请；':'已申请，尚未压缩；')+(result.compaction_request?.reason||args.reason||'原申请原因未记录');
    if(tool==='prepare_compaction')return ({saved:'已选择保存经验',merged:'已合并既有经验',nothing_new:'没有值得新增的经验'})[result.compaction_request?.preparation?.decision]+'；'+(result.compaction_request?.preparation?.assessment||args.assessment||'原判断未记录')+'；等待驱动压缩。';
    if(tool==='save_experience')return result.already_saved===true?'确认已有经验；没有新增或重写记录。':result.experience?.why_now||'读取原保存结果；未给出完整经验内容。';
    if(tool==='report_failure')return String(result.reason||result.category||'原轨迹报告未完成；不作为独立数学裁决');
    if(tool==='set_plan')return '规划节点：'+(args.nodes||[]).map(n=>n.id).join('、');
    if(tool==='add_node')return (args.node?.claim||args.node?.id||node)+(args.needed_by?'；供 '+args.needed_by+' 使用':'');
    if(tool==='probe_proof')return result.open_goal_count!=null?'Lean 返回 '+result.open_goal_count+' 个局部目标；'+(result.new_local_progress?'记录到新进展':'本次检查结果已保存'):'Lean 检查结果已保存';
    if(tool==='review_node')return '审核已有节点 '+node+' 的声明；不新增 DAG 节点，证明状态另计';
    if(tool==='attempt_proof'||tool==='check_node')return node+' 的原证明检查通过';
    if(tool==='get_context')return '读取当前目标、原自然语言证明和可用上下文';
    if(tool==='search_library')return '查询：'+String(args.query||args.names||args.queries||args.keywords||'原检索条件');
    if(tool==='inspect_library')return '查看：'+String(args.names||args.name||'原库声明');
    if(tool==='finalize')return '原最终验收返回通过';
    return result.kind||'原工具返回通过';
  }
  function agentMemory(result) {
    const experience=result?.experience;
    if(result?.ok!==true||result.already_saved!==false||!experience||
       typeof experience.lesson!=='string'||!experience.lesson.trim())return null;
    const outcome=experience.status;
    const label={success:'保存成功经验',failure:'保存失败经验',mixed:'保存恢复／综合经验'}[outcome]||'保存经验';
    return {kind:'selected_experience',label:experience.supersedes?'修订既有经验':label,
      summary:experience.why_now||'原 agent 选择保存该经验。',selected_by:'proof_agent',
      experience:{...experience,outcome,meaning:experience.meaning||'Agent 选择的文字建议；不新增假设，也不构成数学认证。'}};
  }
  function savedMemory(tool,args,result,event,node,{memoryPolicyVersion=1,includeLegacyMemory=false}={}) {
    if(!result||!node)return null;
    const helper=['check_node','attempt_proof'].includes(tool)&&node!=='root';
    const probe=['probe_proof','check_route'].includes(tool);
    const checkedNode=event.graph?.nodes?.find(n=>n.id===node);
    // A completed invoke is written after ProofTools.save. These are annotations
    // of that recorded call, not extra solver tools or independently timed I/O.
    if(helper&&result.ok===true&&!result.already_proved&&result.elaborated_type&&result.source_path){
      const legacy=memoryPolicyVersion<2&&includeLegacyMemory;
      return {kind:'proved_fact',label:legacy?'保存已证事实＋旧版成功经验':'保存已证事实',
        summary:node+' 的精确类型与可复用证明已保存；'+(memoryPolicyVersion<2?(legacy?'同时保留原策略自动记录的成功经验。':'旧版自动经验默认折叠。'):'文字经验由 agent 另行选择。'),
        fact:{node_id:node,claim:checkedNode?.claim||null,statement:args.statement||result.statement||checkedNode?.statement||null,
          elaborated_type:result.elaborated_type,source_path:result.source_path,
          body:args.body||checkedNode?.body||null,depends_on:checkedNode?.depends_on||[]},
        experience:legacy?{outcome:'success',lesson:args.lesson||'Use ProofSteps.'+node+' with its checked binders.',
          selected_by:'legacy_automatic',meaning:'原旧版策略自动保存；不是 agent 主动选择。'}:null};
    }
    if(memoryPolicyVersion>=2||!includeLegacyMemory)return null;
    if(probe&&result.ok===true&&result.new_local_progress===true&&typeof result.prefix==='string'){
      return {kind:'successful_step',label:'旧版自动留存成功步骤',legacy_automatic:true,
        summary:'保留 '+node+' 已检查的证明前缀与 '+result.open_goal_count+' 个剩余局部目标；尚未认证为已证事实。',
        step:{prefix:result.prefix,probe_id:result.probe_id||null,open_goal_count:result.open_goal_count,
          proof_certified:false},experience:null};
    }
    const checkedFailure=['compile_error','proof_action_error','prefix_error','probe_timeout','policy_rejected','shared_module_error'].includes(result.kind);
    if((helper||probe)&&result.ok===false&&checkedFailure&&typeof result.diagnostics==='string'){
      return {kind:'failure_experience',label:'旧版自动留存失败经验',legacy_automatic:true,
        summary:'保存 '+node+' 的 '+result.kind+' 诊断；失败记录不表示命题为假。',
        experience:{outcome:'failure',action:args.tactic||args.body||null,status:result.kind,
          lesson:helper&&args.lesson?args.lesson:result.diagnostics.slice(-1400),
          diagnostics:result.diagnostics,next_action:result.next_action||null,selected_by:'legacy_automatic',
          meaning:probe?'失败动作不替换已检查的证明前缀。':'失败尝试不表示定理为假。'}};
    }
    return null;
  }
  function buildSteps(events,{asOf=null,live=false,memoryPolicyVersion=1,includeLegacyMemory=false}={}) {
    const cutoff=asOf==null?Infinity:time(asOf);const calls=new Map();
    for(const e of events){
      if(!isTool(e))continue;
      const parts=String(e._source_key).split(':');const id=parts.slice(1,-1).join(':');const phase=parts.at(-1);
      const row=calls.get(id)||{id,tool:e.details.tool};
      if(phase==='started')row.start=e;else row.end=e;
      calls.set(id,row);
    }
    const rows=[];
    for(const row of calls.values()){
      const start=row.start||row.end;if(time(start.at)>cutoff)continue;
      const end=row.end&&time(row.end.at)<=cutoff?row.end:null;
      const args=start.details?.arguments||end?.details?.arguments||{};const result=end?.details?.result;
      const node=args.target_id||args.node_id||args.node?.id||(row.tool==='get_context'?result?.current_node?.id:null)||((['attempt_proof','probe_proof','finalize'].includes(row.tool))?'root':null);
      const seconds=end?Number(end.details?.elapsed_seconds??((time(end.at)-time(start.at))/1000)):null;
      const selectedMemory=end&&row.tool==='save_experience'&&memoryPolicyVersion>=2?agentMemory(result):null;
      const label=selectedMemory?.label||(row.tool==='save_experience'?(result?.already_saved===true?'确认已有经验':'选择并保存经验'):row.tool==='attempt_proof'&&node&&node!=='root'?'提交辅助引理':labels[row.tool]||row.tool);
      rows.push({id:row.id,tool:row.tool,stage:stageOf(row.tool),label,node_id:node,
        started_at:row.start?.at||null,at:start.at,completed_at:end?.at||null,
        start_key:start._source_key,end_key:end?._source_key||null,
        duration_seconds:Number.isFinite(seconds)?Math.max(0,seconds):null,
        status:end?statusOf(row.tool,result):asOf!=null||live?'running':'unfinished',
        summary:summaryOf(row.tool,args,result,!!end),diagnostics:end?result?.diagnostics||null:null,
        context_id:node&&node!=='root'?'node:'+node:null,
        ...(selectedMemory?{memory:selectedMemory,source_step_ids:selectedMemory.experience.evidence_ids||[],
          record_details:{...selectedMemory,source_tool:row.tool,source_call_id:row.id,
            timestamp_kind:'source_tool_completion',independent_operation:true}}:{})});
      const memory=end?savedMemory(row.tool,args,result,end,node,{memoryPolicyVersion,includeLegacyMemory}):null;
      if(memory)rows.push({id:'memory:'+row.id,tool:'memory',stage:'memory',label:memory.label,node_id:node,
        at:end.at,started_at:null,completed_at:end.at,start_key:end._source_key,end_key:end._source_key,
        duration_seconds:null,status:'recorded',summary:memory.summary,diagnostics:null,
        context_id:node!=='root'?'node:'+node:null,source_step_id:row.id,memory,
        record_details:{...memory,source_tool:row.tool,source_call_id:row.id,
          evidence:'原工具 completed 日志写入前，ProofTools.invoke 已调用 save；本行为该工具保存结果的可视化展开。',
          timestamp_kind:'source_tool_completion',independent_operation:false}});
    }
    const compressions=new Map();
    for(const e of events){
      const match=String(e._source_key||'').match(/^compression:(\d+):(started|completed)$/);
      if(!match||time(e.at)>cutoff)continue;
      const id='compression:'+match[1],row=compressions.get(id)||{id,index:Number(match[1])+1};
      if(match[2]==='started')row.start=e;else row.end=e;
      compressions.set(id,row);
    }
    const triggers={three_failures:'连续三次 Lean 失败',context_size:'上下文达到压缩阈值',no_progress:'连续三轮无进展',agent_requested:'证明 agent 主动申请'};
    for(const row of compressions.values()){
      const start=row.start||row.end,end=row.end,details=end?.details||row.start?.details||{};
      const trigger=triggers[details.trigger]||details.trigger||'原记录未说明';
      const seconds=end?Number(end.details?.elapsed_seconds??(row.start?(time(end.at)-time(row.start.at))/1000:NaN)):null;
      const completed=end&&end.details?.status==='completed';
      rows.push({id:row.id,tool:'compression',stage:'compression',label:'压缩上下文 #'+row.index,node_id:null,
        at:start.at,started_at:row.start?.at||null,completed_at:end?.at||null,
        start_key:row.start?._source_key||row.end?._source_key,end_key:end?._source_key||null,
        duration_seconds:seconds!=null&&Number.isFinite(seconds)?Math.max(0,seconds):null,
        status:completed?'compacted':end?'compression_incomplete':asOf!=null||live?'compressing':'unfinished',
        summary:'触发原因：'+trigger+(details.reason?'；'+details.reason:'')+'；'+(completed?'原压缩操作已完成，随后可重新读取当前证明上下文。':end?'原记录未确认压缩完成。':'等待原压缩操作结束。'),
        record_details:end?end.details:Object.fromEntries(Object.entries(row.start?.details||{}).filter(([key])=>['turn','trigger','context_tokens','started_at'].includes(key))),
        diagnostics:null});
    }
    for(const e of events){
      if(e.kind!=='unified.replay.completed'||time(e.at)>cutoff)continue;
      rows.push({id:e._source_key,tool:'replay',stage:'verify',label:'独立内核重放',node_id:'root',at:e.at,
        started_at:null,completed_at:e.at,end_key:e._source_key,start_key:e._source_key,
        duration_seconds:e.details?.replay_elapsed_seconds??null,status:e.details?.verified===true?'passed':'failed',
        summary:'读取 unified 原重放结果；没有重新评分',diagnostics:e.details?.diagnostics||null});
    }
    rows.sort((a,b)=>(time(a.at)??0)-(time(b.at)??0)||(a.tool==='memory'?1:0)-(b.tool==='memory'?1:0)||a.id.localeCompare(b.id));
    return rows.map((row,index)=>({...row,ordinal:index+1}));
  }
  function gaps(rows) {
    const out=[];let previous=null;
    for(const row of rows){
      const start=time(row.started_at||row.at);
      if(previous!=null&&start-previous>=15000&&row.tool!=='replay')out.push({before:row.id,seconds:(start-previous)/1000,label:'该间隔无工具活动记录；原日志未明确记录原因'});
      const end=time(row.completed_at||row.started_at||row.at);previous=Math.max(previous??end,end);
    }
    return out;
  }
  function graphStatus(node,{current=false,live=false,runStatus=null}={}) {
    const status=node.status??'unknown';
    const pending=['pending','waiting','queued','ready','planned'].includes(status);
    const executing=['proving','translating_proof','running','in_progress','active'].includes(runStatus);
    return pending&&node.active===true&&current&&live&&executing?'in_progress':status;
  }
  function selectedStep(rows,{selection=null,follow=false,current=false,detailMode='step'}={}) {
    if(!rows.length)return null;
    if(follow&&current&&detailMode==='step')return rows.at(-1).id;
    return rows.some(row=>row.id===selection)?selection:rows.at(-1).id;
  }
  // SVG user units are CSS pixels. Resizing changes the canvas geometry,
  // never the font scale or row height, in either translation view.
  function visitChartMetrics(availableWidth, stageCount) {
    const count=Number.isInteger(stageCount)&&stageCount>0?stageCount:1;
    const minimum=88+Math.max(0,count-1)*76+112+320;
    const width=Math.max(minimum,Number.isFinite(availableWidth)?Math.floor(availableWidth):0);
    const laneGap=count>1?Math.min(96,(width-88-112-320)/(count-1)):0;
    const labelX=88+Math.max(0,count-1)*laneGap+112;
    return {width,top:26,rowHeight:64,headerHeight:44,laneStart:88,laneGap,labelX,labelWidth:width-labelX-20};
  }
  function visitLabel(text, availablePixels) {
    const full=String(text??'');let used=0,out='';
    const limit=Math.max(0,availablePixels-18);
    for(const char of full){
      used+=/[^\u0000-\u00ff]/.test(char)?14:7.5;
      if(used>limit)return out+'…';
      out+=char;
    }
    return full;
  }
  function historyEntries(events,{view='dag',context='main'}={}) {
    const proof=new Set(proofIndices(events));
    return events.flatMap((event,index)=>{
      if(time(event.at)==null||isSnapshot(event))return [];
      const helper=String(event._source_key||'').startsWith('statement:helper:');
      const include=view==='dag'?proof.has(index):context==='main'?
        event.statement_context_id==='main'||!helper&&(event.scope==='main'||String(event._source_key||'').startsWith('statement:')):
        event.statement_context_id===context;
      return include?[{index,at:time(event.at),label:event.title||event.details?.tool||event.kind||'原始事件',key:event._source_key}]:[];
    }).filter((row,index,rows)=>index===rows.length-1||row.at!==rows[index+1].at);
  }
  function indexAtTime(events,at) {
    const cutoff=time(at);let index=-1;
    if(cutoff==null)return index;
    events.forEach((event,i)=>{if(time(event.at)!=null&&time(event.at)<=cutoff)index=i;});
    return index;
  }
  function historicalFrame(initial,current,events,at) {
    const cutoff=time(at),provided=initial.statement?.mode==='provided';
    let nodes=(initial.nodes||[]).map(node=>({...node,...(!provided?{statement:'',body:''}:{})}));
    let pipeline=initial.pipeline||[],statement=initial.statement,evidence='reconstructed',graphAt=null,status=null;
    let contexts=statement?[{id:'main',kind:'main',node_id:'root',label:'主定理',data:statement}]:[];
    for(const event of events){
      if(time(event.at)==null||time(event.at)>cutoff)continue;
      if(Array.isArray(event.graph?.nodes)){nodes=event.graph.nodes;evidence=event.graph.evidence||'reconstructed';graphAt=event.at;}
      if(Array.isArray(event.pipeline))pipeline=event.pipeline;
      if(isSnapshot(event)&&event.details?.status)status=event.details.status;
      if(event.scope==='main'&&event.statement)status='translating_main';
      if(event.scope==='proof'&&!isSnapshot(event)){
        status='proving';
        if(!Array.isArray(event.pipeline))pipeline=pipeline.map(stage=>stage.id==='helpers'?{...stage,status:'running'}:stage);
      }
      const result=event.details?.result,tool=event.details?.tool;
      if(tool==='report_failure'&&result?.ok===true&&result.status==='translation_failed')status='translation_failed';
      if(tool==='finalize'&&result?.ok===true&&result.status==='completed')status='completed';
      if(event.kind==='unified.replay.completed')status=event.details?.verified===true?'completed':'replay_failed';
      if(event.statement_contexts)contexts=event.statement_contexts;
      if(event.statement){
        const id=event.statement_context_id||'main';
        const metadata=event.statement_context||contexts.find(c=>c.id===id)||{id,kind:'main',node_id:'root',label:'主定理'};
        contexts=[...contexts.filter(c=>c.id!==id),{...metadata,data:event.statement}];
        if(id==='main')statement=event.statement;
      }
    }
    function hydrate(data,latest){
      if(!data)return data;
      const artifacts=data.artifact_ids?(latest?.artifacts||[]).filter(a=>data.artifact_ids.includes(a.id)):data.artifacts||[];
      return {...data,artifacts:artifacts.filter(a=>time(a.at)!=null&&time(a.at)<=cutoff),
        operations:(data.operations||[]).filter(a=>time(a.at)!=null&&time(a.at)<=cutoff),
        ...(data.trace?{trace:{...data.trace,visits:(data.trace.visits||[]).filter(a=>time(a.at)!=null&&time(a.at)<=cutoff)}}:{})};
    }
    statement=hydrate(statement,current.statement);
    contexts=contexts.map(c=>({...c,data:hydrate(c.data,(current.statement_contexts||[]).find(n=>n.id===c.id)?.data)}));
    return {nodes,pipeline,statement,contexts,evidence,graphAt,status};
  }
  return {stages,chronological,proofIndices,isSnapshot,buildSteps,gaps,time,graphStatus,selectedStep,visitChartMetrics,visitLabel,historyEntries,indexAtTime,historicalFrame};
});

(() => {
  'use strict';
  const $ = id => document.getElementById(id);
  // Deployment config: same-origin by default; GitHub Pages sets window.VIS_CONFIG via config.js.
  const CONFIG = Object.assign({ apiBase: '', token: '', credentials: false }, window.VIS_CONFIG || {});
  const pageToken = new URL(location.href).searchParams.get('token') || '';
  function apiUrl(path) {
    if (CONFIG.static) {
      const query = new URL(path, 'http://static.invalid').searchParams;
      if (path.startsWith('/api/runs')) return 'data/runs.json';
      if (path.startsWith('/api/run')) return 'data/runs/' + encodeURIComponent(query.get('id') || '') + '.json';
      if (path.startsWith('/api/final-code')) return 'data/final-code/' + encodeURIComponent(query.get('id') || '') + '.json';
    }
    const url = new URL(path, CONFIG.apiBase || location.href);
    const token = CONFIG.token || pageToken;
    if (token) url.searchParams.set('token', token);
    return url.toString();
  }
  const NS = 'http://www.w3.org/2000/svg';
  const W = 196, H = 116;
  const state = {
    finalCode: null, finalCodeKey: null, finalCodeFile: null, finalCodeController: null,
    runs: [], data: null, events: [], frame: null, selected: null,
    cursorIndex: -1, cursorTime: null, showCurrent: true, follow: false, unread: 0,
    codeTab: 'statement',
    stream: null, request: 0, controller: null, layout: null,
    transform: { x: 0, y: 0, scale: 1 }, manualTransform: false, needsFit: true,
    dragging: null, noticeTimer: null, statementStage: null, statementArtifact: null, statementExpanded: true,
    view: 'dag', statementContext: 'main', proofSelection:null, proofLimit:100, proofDetailMode:'step', showLegacyMemory:false
  };

  const statusNames = {
    waiting_for_dependencies: '准备运行依赖', preparing_resources: '准备任务环境',
    translating_main: '主声明转译中', main_locked: '主声明已锁定', translating_proof: '证明转译中',
    verifying_export: '独立重放验收中', main_incomplete: '主声明未完成', proof_incomplete: '证明未完成',
    replay_incomplete: '重放未完成',
    pending: '待处理', waiting: '等待中', queued: '排队中', planned: '已规划',
    proving: '证明中', running: '运行中', active: '进行中', in_progress: '进行中',
    admitted: '已准入', locked: '已锁定', checked: '已检查', ready: '已就绪',
    proved: '已证明', proven: '已证明', verified: '已验证', accepted: '已接受',
    done: '完成', complete: '完成', completed: '完成', success: '成功', passed: '通过',
    failed: '失败', error: '错误', rejected: '已拒绝', blocked: '受阻',
    infrastructure_error: '基础设施错误', verification_pending: '等待验证',
    proof_failed: '证明失败', main_failed: '主定理失败', replay_failed: '重放失败',
    budget_exhausted: '预算耗尽', candidate_failed: '候选失败',
    translation_failed: '证明转译未完成', incomplete: '未完成', stopped: '已停止',
    source_review: '语义审核中', closed: '局部闭合', cancelled: '已取消',
    paused: '已暂停', not_started: '未开始', skipped: '已跳过', provided: '已提供',
    kernel_proved: 'Kernel 已通过', export_verified: '导出已验证', unknown: '未记录',
    compacted: '已压缩', compressing: '压缩中', compression_incomplete: '压缩未完成',
    returned: '已返回', progress: '检查返回（仍有目标）', unfinished: '未记录结束', recorded: '已有记录', registered: '已登记', confirmed: '已绑定', reuse: '检索到可复用项', compose: '检索到组合项',
    bridge_miss: '存在库缺口', unchecked: '未检查草稿', machine_gate_passed: '定义编译通过',
    machine_gate_rejected: '编译拒绝', elaborated_with_placeholder: '声明编译通过',
    elaboration_failed: '声明编译未通过', accept: '语义接受', revise: '需要修订',
    revise_or_abstain: '修订 / 未决', checker_timeout: '检查超时', checker_error: '检查基础设施错误',
    tool_rejected: '工具未通过', locked_model_aligned: '声明已锁定', elaboration_error: '声明编译未通过', requested: '已提出需求'
  };
  const normalizedStatus = value => String(value ?? 'unknown').toLowerCase().replace(/[ -]/g, '_');
  function tone(value) {
    const status = normalizedStatus(value);
    if (['proved', 'proven', 'accepted', 'verified', 'success', 'done', 'complete', 'completed', 'passed',
      'accept', 'admitted', 'locked', 'locked_model_aligned', 'machine_gate_passed', 'elaborated_with_placeholder'].includes(status)) return 'proved';
    if (['revise', 'revise_or_abstain', 'bridge_miss'].includes(status)) return 'failed';
    if (/failed|error|reject|blocked|exhausted/.test(status)) return 'failed';
    if (['proving', 'running', 'active', 'in_progress', 'compressing', 'verification_pending', 'source_review', 'closed', 'queued', 'kernel_proved', 'export_verified'].includes(status)) return 'active';
    return 'pending';
  }
  const statusText = value => statusNames[normalizedStatus(value)] || String(value ?? '未记录');
  const isRoot = node => String(node.id) === 'root' || node.is_root === true || node.kind === 'root' || node.role === 'root';
  const display = value => value == null ? '—' : typeof value === 'object' ? JSON.stringify(value) : String(value);
  const asList = value => Array.isArray(value) ? value : [];
  const dependencies = node => asList(node.depends_on).map(item => String(typeof item === 'object' && item !== null ? item.id : item));
  const nodeId = node => String(node.id);
  const nodeClaim = node => String(node.claim ?? node.nl_claim ?? node.title ?? '此帧未记录自然语言 claim');
  function el(tag, className, text) {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text != null) node.textContent = String(text);
    return node;
  }
  function svg(tag, attributes = {}, text) {
    const node = document.createElementNS(NS, tag);
    Object.entries(attributes).forEach(([key, value]) => node.setAttribute(key, value));
    if (text != null) node.textContent = String(text);
    return node;
  }
  function humanTime(value, full = false) {
    const date = parseTime(value);
    if (date == null) return '时间未记录';
    return new Date(date).toLocaleString('zh-CN', {
      ...(full ? { month: '2-digit', day: '2-digit' } : {}),
      hour: '2-digit', minute: '2-digit', second: '2-digit', hour12: false
    });
  }
  function parseTime(value) {
    if (value == null || value === '') return null;
    let timestamp;
    if (typeof value === 'number') timestamp = value < 1e11 ? value * 1000 : value;
    else timestamp = Date.parse(value);
    return Number.isFinite(timestamp) ? timestamp : null;
  }
  function duration(ms) {
    const seconds = Math.max(0, Math.floor(ms / 1000));
    const h = Math.floor(seconds / 3600), m = Math.floor(seconds % 3600 / 60), s = seconds % 60;
    return h ? `${h}h ${String(m).padStart(2, '0')}m` : `${m}m ${String(s).padStart(2, '0')}s`;
  }
  function notice(message, permanent = false) {
    clearTimeout(state.noticeTimer);
    const node = $('notice');
    node.replaceChildren(el('span', '', message));
    const close = el('button', '', '关闭');
    close.addEventListener('click', () => { node.hidden = true; });
    node.append(close);
    node.hidden = false;
    if (!permanent) state.noticeTimer = setTimeout(() => { node.hidden = true; }, 7000);
  }
  function connection(mode, text) {
    $('connection').dataset.state = mode;
    $('connection').lastElementChild.textContent = text;
  }
  async function fetchJSON(url, signal) {
    const response = await fetch(apiUrl(url), { signal, headers: { Accept: 'application/json' }, cache: 'no-store', credentials: CONFIG.credentials ? 'include' : 'same-origin' });
    if (!response.ok) throw new Error(`HTTP ${response.status} · ${url.split('?')[0]}`);
    return response.json();
  }
  function runOptionText(run) {
    return `${run.live ? '● LIVE' : '历史'}  ·  ${run.title || run.id}  ·  ${statusText(run.status)}`;
  }
  function syncRunOption(run) {
    const recorded = state.runs.find(item => String(item.id) === String(run.id));
    if (recorded) Object.assign(recorded, run);
    const option = [...$('run-select').options].find(item => item.value === String(run.id));
    if (option) option.textContent = runOptionText(run);
  }
  async function loadRuns() {
    $('refresh-runs').disabled = true;
    try {
      const payload = await fetchJSON('/api/runs');
      if (!Array.isArray(payload.runs)) throw new Error('/api/runs 未返回 runs 数组');
      state.runs = payload.runs;
      const picker = $('run-select');
      picker.replaceChildren();
      state.runs.forEach(run => {
        const option = el('option', '', runOptionText(run));
        option.value = String(run.id);
        picker.append(option);
      });
      picker.disabled = !state.runs.length;
      if (!state.runs.length) {
        picker.append(el('option', '', '暂无可读取的运行'));
        connection('idle', '未发现运行');
        $('run-title').textContent = '暂无可读取的运行';
        $('graph-empty').querySelector('p').textContent = '数据源未返回运行记录。刷新列表后可继续查看。';
      } else if (!state.data) {
        const wanted = new URL(location.href).searchParams.get('id');
        const chosen = state.runs.find(run => String(run.id) === wanted)
          || state.runs.find(run => String(run.id) === 'live-201') || state.runs.find(run => run.live) || state.runs[0];
        await loadRun(String(chosen.id));
      } else {
        const selected = state.runs.find(run => String(run.id) === String(state.data.run.id));
        if (selected) picker.value = String(selected.id);
        else {
          const option = el('option', '', state.data.run.title || state.data.run.id);
          option.value = String(state.data.run.id);
          picker.append(option); picker.value = option.value;
        }
      }
    } catch (error) {
      connection('error', '数据源不可用');
      notice(`无法读取运行列表：${error.message}。页面需要连接提供 /api 的本地服务。`, true);
      if (!state.data) {
        $('run-title').textContent = '等待数据源连接';
        $('run-select').replaceChildren(el('option', '', '运行列表读取失败'));
        $('graph-empty').querySelector('p').textContent = '未载入任何案例数据。请确认本地 API 服务已经启动。';
      }
    } finally {
      $('refresh-runs').disabled = false;
      $('app').setAttribute('aria-busy', 'false');
    }
  }
  async function loadRun(id, options = {}) {
    const request = ++state.request;
    state.finalCodeController?.abort();state.finalCodeController=null;state.finalCode=null;state.finalCodeKey=null;state.finalCodeFile=null;
    $('final-code-panel').open=false;
    state.controller?.abort(); state.stream?.close(); state.stream = null;
    state.controller = new AbortController();
    $('app').setAttribute('aria-busy', 'true');
    connection('loading', '读取运行记录');
    try {
      const payload = await fetchJSON(`/api/run?id=${encodeURIComponent(id)}`, state.controller.signal);
      if (request !== state.request) return;
      if (!payload.run || !payload.current) throw new Error('运行详情缺少 run 或 current 字段');
      state.data = { ...payload, initial: payload.initial || { nodes: [], pipeline: [] }, stats: payload.stats || {} };
      state.events = mergeEvents([], payload.events);
      
      state.cursorTime=null;state.showCurrent = true; state.follow = !!payload.run.live && !CONFIG.static; state.unread = 0;
      state.cursorIndex = state.events.length - 1;
      state.needsFit = true; state.manualTransform = false;
      state.statementStage = null; state.statementArtifact = null;
      state.proofSelection=null;state.proofLimit=100;state.proofDetailMode='step';state.showLegacyMemory=false;
      const query = new URL(location.href).searchParams;
      state.view = options.view || (query.get('id') === id ? query.get('view') : null)
        || (payload.current.statement?.mode === 'translated' ? 'statement' : 'dag');
      state.statementContext = options.context || (query.get('id') === id ? query.get('context') : null) || 'main';
      state.statementExpanded = payload.current.statement?.mode !== 'provided';
      const nodes = asList(payload.current.nodes);
      const requestedNode = asList(payload.current.statement_contexts).find(c => c.id === state.statementContext)?.node_id;
      state.selected = nodes.length ? nodeId(nodes.find(n => nodeId(n) === requestedNode) || nodes.find(isRoot) || nodes[0]) : null;
      $('run-select').value = id;
      const requestedTime=parseTime(query.get('at'));
      if(requestedTime!=null){state.cursorTime=requestedTime;state.cursorIndex=ProofTrace.indexAtTime(state.events,requestedTime);state.showCurrent=false;state.follow=false;}
      if (options.history !== false) updateLocation(options.history === 'push');
      $('notice').hidden = true;
      renderHeader(); renderFrame();  renderSnapshotControl();
      if (payload.run.live) connectStream(id, request);
      else connection('idle', '历史记录已载入');
    } catch (error) {
      if (error.name === 'AbortError' || request !== state.request) return;
      connection('error', '详情读取失败');
      notice(`无法读取运行 ${id}：${error.message}`, true);
      if (state.data) $('run-select').value = String(state.data.run.id);
    } finally {
      if (request === state.request) $('app').setAttribute('aria-busy', 'false');
    }
  }
  function mergeEvents(previous, incoming) { return ProofTrace.chronological(previous, incoming); }
  function connectStream(id, request) {
    if (CONFIG.static) return;
    const last = state.events.reduce((max,e)=>Math.max(max,Number(e.seq)), -1);
    const stream = new EventSource(apiUrl(`/api/stream?id=${encodeURIComponent(id)}&after=${encodeURIComponent(last)}`), { withCredentials: !!CONFIG.credentials });
    state.stream = stream;
    stream.onopen = () => { if (request === state.request) connection('live', '实时连接已附着'); };
    stream.onerror = () => { if (request === state.request) connection('error', '连接中断 · 重连中'); };
    stream.addEventListener('update', message => {
      if (request !== state.request) return;
      try {
        const update = JSON.parse(message.data);
        const oldCount = state.events.length;
        // Keep the playback coordinate at the same recorded instant when the tail grows.
        const anchor = state.events[state.cursorIndex]?._source_key;
        state.events = mergeEvents(state.events, update.events);
        const added = state.events.length - oldCount;
        state.data.current = update.current || state.data.current;
        state.data.stats = { ...state.data.stats, ...(update.stats || {}) };
        state.data.run = { ...state.data.run, ...(update.run || {}) };
        
        if (state.follow) {
          state.showCurrent = true; state.cursorIndex = state.events.length - 1;
        } else {
          state.unread += Math.max(0, added);
          const anchored=state.events.findIndex(e=>e._source_key===anchor);
          if(state.cursorTime!=null)state.cursorIndex=ProofTrace.indexAtTime(state.events,state.cursorTime);else if(anchored>=0)state.cursorIndex=anchored;
        }
        renderHeader();
        renderFrame();
         renderSnapshotControl();
        if (!state.data.run.live) {
          stream.close(); state.stream = null; state.follow = false;
          connection('idle', '运行已进入终态'); renderSnapshotControl();
        }
      } catch (error) {
        connection('error', '更新解析失败');
        console.error('Invalid run update', error);
      }
    });
  }
  function renderHeader() {
    const { run, current, stats } = state.data;
    syncRunOption(run);
    $('mode-badge').textContent = run.live ? 'LIVE / 实时' : 'ARCHIVE / 历史';
    $('mode-badge').classList.toggle('live', !!run.live);
    $('run-id').textContent = run.id;
    $('run-title').textContent = run.title || run.id;
    $('metric-attempts').textContent = display(current.probe_attempts ?? stats.probe_attempts);
    $('metric-attempts').nextElementSibling.textContent = 'Probe 次数（当前累计）';
    $('run-status').textContent = statusText(current.status ?? run.status);
    $('run-status').title = `来源状态：${display(current.status ?? run.status)}；不由辅助节点数量推断`;
    $('source-scope').textContent = `SOURCE SCOPE · ${display(run.scope)}`;
    $('source-path').textContent = run.source_path || '此运行未提供来源路径';
    $('history-notice').textContent = run.history_notice || '历史图仅应用已记录的 graph / pipeline 快照；未记录的中间状态不作补造。实时快照单独标识。';
    $('history-kind').textContent = '点选操作查看当时状态';
    renderTermination(current.termination);
  }
  function renderTermination(termination) {
    let banner = $('termination-summary');
    if (!banner) {
      banner = el('section', 'termination-summary'); banner.id = 'termination-summary';
      banner.setAttribute('aria-label', '运行结束原因');
      document.querySelector('.run-heading').insertAdjacentElement('afterend', banner);
    }
    banner.hidden = !termination;
    banner.replaceChildren();
    if (!termination) return;
    banner.append(el('strong', '', `${statusText(termination.status)} · 流程已结束`));
    const failure = termination.translation_failure;
    if (failure) {
      banner.append(el('p', 'termination-provenance', `模型原始报告 · ${display(failure.category)} · 此处展示原报告，不作为独立数学裁决。`));
      if (failure.reason) banner.append(el('p', 'termination-reason', failure.reason));
      if (failure.cited_names?.length) banner.append(el('p', 'termination-provenance', `原报告引用：${failure.cited_names.join('，')}`));
    }
    const meta = [];
    if (failure?.reported_at) meta.push(`报告时间 ${humanTime(failure.reported_at, true)}`);
    if (termination.controller?.exit_code != null) meta.push(`原 worker 退出码 ${termination.controller.exit_code}`);
    if (termination.native_stop_reason) meta.push(`原停止状态 ${termination.native_stop_reason}`);
    if (meta.length) banner.append(el('p', 'termination-provenance', meta.join(' · ')));
  }
  function frameAtCursor() {
    if (state.showCurrent) return { nodes: asList(state.data.current.nodes), pipeline: asList(state.data.current.pipeline), statement: state.data.current.statement, contexts: asList(state.data.current.statement_contexts), evidence: 'current' };
    return ProofTrace.historicalFrame(state.data.initial,state.data.current,state.events,state.cursorTime??state.events[state.cursorIndex]?.at);
  }

  function updateLocation(push = false) {
    const url = new URL(location.href);
    url.searchParams.set('id', state.data.run.id); url.searchParams.set('view', state.view);
    if (state.statementContext !== 'main') url.searchParams.set('context', state.statementContext);
    else url.searchParams.delete('context');
    if(!state.showCurrent&&state.cursorTime!=null)url.searchParams.set('at',new Date(state.cursorTime).toISOString());else url.searchParams.delete('at');
    if (url.href !== location.href) history[push ? 'pushState' : 'replaceState'](null, '', url);
  }
  function switchView(view, context = state.statementContext, push = true) {
    if(!state.data||!state.frame)return;
    state.view = view; state.statementContext = context; state.statementExpanded = true;
    if (view === 'dag') {
      const source = asList(state.frame.contexts).find(c => c.id === context);
      if (source?.node_id) state.selected = source.node_id;
      state.needsFit = !state.manualTransform;
    }
    updateLocation(push); renderFrame();renderSnapshotControl();
  }
  function renderNavigation() {
    ['statement','dag'].forEach(view => $('view-' + view).setAttribute('aria-selected', String(view === state.view)));
    const host = $('related-runs'); host.replaceChildren();
    asList(state.data.run.related_runs).forEach(link => {
      if (!state.runs.some(run => run.id === link.id)) return;
      const a = el('a', 'related-run-link', link.label);
      a.href = `/?id=${encodeURIComponent(link.id)}&view=${encodeURIComponent(link.view || 'dag')}`;
      a.title = '切换到同题的另一份独立运行；不合并两个实验的轨迹或结论';
      a.addEventListener('click', event => { event.preventDefault(); loadRun(link.id, {view:link.view || 'dag', history:'push'}); });
      host.append(a);
    });
    $('view-context').textContent = state.view === 'statement'
      ? '定理转译 · 沿实际检索、候选、编译反馈与审核记录追踪；可从辅助节点进入并返回原 DAG。'
      : '证明转译 · 沿真实调用查看拆解、检索、证明和修复；上方查看命题依赖，下方回看每次操作；节点定理转译可进入 01。';
  }
  function renderFrame() {
    if (!state.data) return;
    state.frame = frameAtCursor();
    const helpers = state.frame.nodes.filter(node => !isRoot(node));
    $('metric-nodes').textContent = `${helpers.filter(node => tone(node.status) === 'proved').length}/${helpers.length}`;
    $('metric-nodes').nextElementSibling.textContent = state.showCurrent ? '辅助节点已证明（当前）' : '辅助节点已证明（此帧）';
    $('metric-nodes').title = '由所选帧的真实图计算；最终目标状态独立显示';
    $('metric-compressions').textContent = state.showCurrent ? display(state.data.current.compressions ?? state.data.stats.compressions)
      : String(compressionCount(state.events.slice(0, state.cursorIndex + 1)));
    $('metric-compressions').nextElementSibling.textContent = state.showCurrent ? '上下文压缩（当前累计）' : '上下文压缩（至此帧）';
    const pipeline = $('pipeline'); pipeline.replaceChildren();
    state.frame.pipeline.forEach((stage, index) => {
      const status = tone(stage.status), item = el('li', `tone-${status}`);
      item.title = `${stage.label || stage.id}：${statusText(stage.status)}（${display(stage.status)}）`;
      item.append(el('span', 'stage-indicator', status === 'proved' ? '✓' : status === 'failed' ? '!' : String(index + 1).padStart(2, '0')),
        el('span', 'stage-label', stage.label || stage.id));
      if (['statement','helpers'].includes(stage.id)) {
        item.tabIndex = 0; item.setAttribute('role', 'button'); item.setAttribute('aria-controls', stage.id === 'statement' ? 'statement-panel' : 'dag-trace-panel');
        const open = () => switchView(stage.id === 'statement' ? 'statement' : 'dag', 'main');
        item.addEventListener('click', open);
        item.addEventListener('keydown', event => { if (event.key === 'Enter' || event.key === ' ') { event.preventDefault(); open(); } });
      }
      pipeline.append(item);
    });
    if (!state.frame.pipeline.length) pipeline.append(el('li', 'muted', '该帧未记录阶段状态'));
    $('pipeline-frame').textContent = state.showCurrent ? (state.data.run.live ? '实时快照' : '最终快照') : humanTime(state.cursorTime,true)+' · 历史';
    renderTermination(state.showCurrent?state.data.current.termination:null);
    $('run-status').textContent=state.showCurrent?statusText(state.data.current.status??state.data.run.status):state.frame.status?statusText(state.frame.status):'历史记录';
    $('run-status').nextElementSibling.textContent=state.showCurrent?'当前运行状态':'所选时刻状态';
    $('run-status').title=state.showCurrent?'原记录当前状态':'仅显示所选时刻之前的记录';
    const evidenceLabels = { observed: '记录快照 · OBSERVED', reconstructed: '事件重建 · RECONSTRUCTED', current: state.data.run.live ? '当前快照 · CURRENT' : '最终快照 · CURRENT' };
    $('graph-evidence').textContent = evidenceLabels[state.frame.evidence] || `证据 · ${state.frame.evidence}`;
    $('graph-evidence').classList.toggle('reconstructed', state.frame.evidence === 'reconstructed');
    const statementOnly = state.frame.statement?.mode === 'translated' && !helpers.length
      && state.frame.pipeline.find(stage => stage.id === 'helpers')?.status === 'pending';
    document.querySelector('.workspace').hidden = state.view !== 'dag';
    $('proof-wait-note').hidden = state.view !== 'dag' || !statementOnly;
    $('proof-wait-note').textContent = state.data.run.status === 'cancelled'
      ? '本运行在主声明阶段已取消，没有启动 DAG 证明。上方可打开同题的独立 DAG 运行；两份轨迹不会合并。'
      : '本运行的 DAG 证明尚未启动；先完成主声明审核和锁定。';
    if (statementOnly) {
      const declarations = asList(state.frame.statement.artifacts).filter(a => a.kind === 'theorems');
      $('metric-nodes').textContent = `${declarations.filter(a => a.status === 'elaborated_with_placeholder').length}/${declarations.length}`;
      $('metric-nodes').nextElementSibling.textContent = '主声明编译通过';
      $('metric-nodes').title = '声明编译记录，不代表语义审核或证明通过';
      $('metric-attempts').textContent = asList(state.frame.statement.operations).length;
      $('metric-attempts').nextElementSibling.textContent = '定理转译工具结果';
    } else {
      $('metric-attempts').textContent = state.showCurrent?display(state.data.current.probe_attempts??state.data.stats.probe_attempts):state.events.slice(0,state.cursorIndex+1).filter(e=>e.details?.tool==='probe_proof'&&String(e._source_key).endsWith(':completed')).length;
      $('metric-attempts').nextElementSibling.textContent=state.showCurrent?'Probe 次数（当前累计）':'Probe 次数（至此时刻）';
    }
    if (!state.showCurrent) {
      const event = state.events[state.cursorIndex];
      if (String(event?.kind).startsWith('statement.')&&(event.statement_context_id||'main')===state.statementContext) {
        state.statementStage = event.details?.stage || state.statementStage;
        state.statementArtifact = event.details?.artifact?.id || event.details?.operation_record_id || null;
        // Preserve the user-selected translation object while seeking time.
      }
    }
    renderNavigation(); renderStatement(); renderFinalCode();
    $('dag-trace-panel').hidden=state.view!=='dag';$('proof-map').hidden=state.view!=='dag';
    if(state.view==='dag')renderProofTrace();
    if (state.view === 'dag') renderGraph();
  }

  function renderFinalCode() {
    $('final-code-panel').hidden=!state.showCurrent;
    const meta=state.data?.current.final_code,key=state.data?state.data.run.id+':'+(meta?.sha256||'pending'):null;
    if(key!==state.finalCodeKey){state.finalCodeController?.abort();state.finalCodeController=null;state.finalCode=null;state.finalCodeFile=null;state.finalCodeKey=key;}
    $('final-code-status').textContent=meta?.available?`已验证 · ${meta.file_count} 个完整文件`:'尚无已验证的最终代码';
    $('final-code-note').textContent=meta?.message||'展开后读取本次运行的最终导出。';
    const files=$('final-code-files');files.replaceChildren();
    $('final-code-copy').disabled=!state.finalCode?.files?.length;
    const download=$('final-code-download');download.hidden=!meta?.available;
    download.href=state.data?apiUrl('/api/final-code?id='+encodeURIComponent(state.data.run.id)+'&download=1'):'#';
    if(state.finalCode?.files?.length){
      state.finalCodeFile=state.finalCode.files.some(f=>f.name===state.finalCodeFile)?state.finalCodeFile:state.finalCode.entrypoint;
      state.finalCode.files.forEach(file=>{
        const button=el('button','final-code-file',file.name+' · '+file.label);
        button.setAttribute('aria-pressed',String(file.name===state.finalCodeFile));
        button.addEventListener('click',()=>{state.finalCodeFile=file.name;renderFinalCode();});files.append(button);
      });
      const file=state.finalCode.files.find(f=>f.name===state.finalCodeFile)||state.finalCode.files[0];
      $('final-code-source').textContent=file.content;
      $('final-code-meta').textContent=`${file.lines} 行 · ${file.bytes.toLocaleString()} 字节 · SHA256 ${file.sha256}`;
    }else{
      $('final-code-source').textContent='';$('final-code-meta').textContent='';
      if($('final-code-panel').open&&meta?.available&&!state.finalCodeController)loadFinalCode();
    }
  }
  async function loadFinalCode(){
    if(!state.data?.current.final_code?.available)return;
    const key=state.finalCodeKey,id=state.data.run.id,controller=new AbortController();state.finalCodeController=controller;
    $('final-code-note').textContent='读取已验证的完整文件…';
    try{
      const value=await fetchJSON('/api/final-code?id='+encodeURIComponent(id),controller.signal);
      if(key!==state.finalCodeKey||id!==state.data?.run.id)return;
      if(value.sha256!==state.data.current.final_code.sha256||!value.available||!value.verified)throw new Error('文件与当前已验证导出不一致');
      state.finalCode=value;state.finalCodeFile=value.entrypoint;renderFinalCode();
    }catch(error){if(error.name!=='AbortError'&&key===state.finalCodeKey)$('final-code-note').textContent='暂时无法读取：'+error.message+'。重新展开可再次读取。';}
    finally{if(state.finalCodeController===controller)state.finalCodeController=null;}
  }
  function statementContextMode(context) {
    if (context?.kind !== 'helper') return 'main';
    if (context.has_records || context.data?.artifacts?.length || context.data?.operations?.length) return 'full';
    return context.route === 'local' ? 'local' : 'pending';
  }
  function renderStatement() {
    const contexts = asList(state.frame.contexts);
    const context = contexts.find(c => c.id === state.statementContext) || contexts.find(c => c.id === 'main');
    const data = context?.data || state.frame.statement, panel = $('statement-panel');
    panel.hidden = state.view !== 'statement' || !data;
    if (!data) return;
    const picker = $('statement-context-select'); picker.replaceChildren();
    const contextGroups = [['main','主定理'],['full','已运行完整转译 / 审核'],['pending','待完整转译 / 审核'],['local','局部声明检查 · 未调用独立转译']];
    contextGroups.forEach(([mode,label])=>{
      const matches=contexts.filter(c=>statementContextMode(c)===mode);if(!matches.length)return;
      const group=el('optgroup','');group.label=label+`（${matches.length}）`;
      matches.forEach(c=>{const option=el('option','',mode==='main'?(c.label||c.id):c.node_id+' · '+(mode==='local'?'局部检查':mode==='full'?'完整转译 / 审核':'尚无独立转译记录'));option.value=c.id;group.append(option);});picker.append(group);
    });
    picker.value = context?.id || 'main';
    $('statement-back-to-dag').textContent = `返回 DAG · ${context?.node_id || 'root'} ↗`;
    const localOnly=statementContextMode(context)==='local';
    $('statement-title').textContent = context?.kind === 'helper' ? `节点 ${context.node_id} · ${localOnly?'局部声明检查':'定理转译'}` : '定理转译';
    const provided = data.mode === 'provided', artifacts = asList(data.artifacts), calls = asList(data.operations);
    const records = [...artifacts, ...calls].sort((a,b) => a.at.localeCompare(b.at));
    if(!localOnly)renderExecutionTrace(data, records);else $('statement-trace-panel').hidden=true;
    $('statement-local-panel').hidden=!localOnly;$('statement-steps').hidden=localOnly;
    $('statement-content').querySelector('.statement-workbench').hidden=localOnly;
    const bridge = $('statement-bridge'); bridge.replaceChildren();
    if (context?.kind === 'helper') {
      bridge.append(el('strong', '', `DAG ${context.node_id} → ${localOnly?'局部声明检查':'本节点的声明审核'}`),
        el('span', '', context.has_records ? '由 review_node 的原产物目录精确关联；返回后继续查看同一节点的证明。' : data.note));
      const calls = asList(context.invocations).filter(c => c.tool === 'review_node');
      if (calls.length) bridge.append(el('span', 'mono', `原调用 ${[...new Set(calls.map(c => c.call_id))].join(' · ')}`));
    } else {
      bridge.append(el('strong', '', data.mode === 'provided' ? '数据集给定 Lean 声明 → DAG root' : '主声明审核 / 锁定 → DAG root'),
        el('span', '', data.mode === 'provided' ? '直接使用给定目标；不重新转译主声明。'
          : artifacts.some(a => a.kind === 'locked-targets') ? '锁定记录与后续证明分列；点击返回 DAG 查看根目标。' : '当前没有声明锁定记录；本运行的 DAG 尚未启动。'));
    }
    $('statement-mode').textContent = localOnly ? 'LOCAL · 未调用独立转译' : provided ? '给定 Lean · 跳过转译' : `${artifacts.length} 份产物 · ${calls.length} 次工具结果 · ${state.showCurrent ? '当前快照' : '至此事件'}`;
    $('statement-note').textContent = localOnly?'本节点的 Lean 声明由证明模型在 DAG 中提出，采用局部 Lean 检查。本次没有调用独立的检索、语义审核和锁定流程，因此没有该流水线的执行轨迹。':`${data.status === 'cancelled' ? '本运行已取消；以下显示历史产物和原工具调用记录。' : ''}${data.note || ''}`;
    $('statement-content').hidden = !state.statementExpanded;
    $('statement-toggle').textContent = state.statementExpanded ? '收起详情 −' : provided ? '查看给定声明 +' : '展开转译流程 +';
    $('statement-toggle').setAttribute('aria-expanded', String(state.statementExpanded));
    if(localOnly){
      const localHost=$('statement-local-panel');localHost.replaceChildren();
      localHost.append(el('h3','','这里没有运行独立定理转译'),el('p','detail-muted','逐步检索、Lean 探测、修复和证明属于本节点的 DAG 执行记录。点击“返回 DAG”查看同一个节点。'));
      const node=state.frame.nodes.find(n=>nodeId(n)===context.node_id);
      if(node?.statement)localHost.append(el('h4','','本节点实际记录的声明'),el('pre','lean-code',node.statement));
      $('statement-trace-count').textContent='未调用独立转译';return;
    }
    const steps = asList(data.steps), host = $('statement-steps'); host.replaceChildren();
    if (!state.statementStage) state.statementStage = provided ? 'source'
      : asList(data.active_operations).at(-1)?.stage || artifacts.at(-1)?.stage || 'source';
    steps.forEach((step, index) => {
      const item = el('li', `statement-step tone-${tone(step.status)}`), button = el('button', '');
      button.setAttribute('aria-pressed', String(step.id === state.statementStage));
      button.append(el('span', 'mono', String(index + 1).padStart(2, '0')), el('strong', '', step.label),
        el('span', 'statement-step-status', `${statusText(step.status)}${step.count ? ` · ${step.count}` : ''}`));
      button.addEventListener('click', () => { state.statementStage = step.id; state.statementArtifact = null; renderStatement(); });
      item.append(button); host.append(item);
    });
    const list = $('statement-artifacts'); list.replaceChildren();
    const stage = steps.find(s => s.id === state.statementStage), selected = records.filter(a => a.stage === state.statementStage).reverse();
    const recordLabel = artifact => artifact.kind === 'operations' && artifact.data?.phase === 'submitted'
      ? '已提交（原记录）' : statusText(artifact.status);
    const recordTone = artifact => artifact.kind === 'operations' && artifact.data?.phase === 'submitted'
      ? 'pending' : tone(artifact.status);
    list.append(el('h3', '', `${stage?.label || '阶段记录'} / ${selected.length}`));
    selected.forEach(artifact => {
      const button = el('button', `statement-artifact${artifact.id === state.statementArtifact ? ' selected' : ''}`);
      button.append(el('span', 'statement-artifact-label', artifact.label), el('strong', 'mono', artifact.id),
        el('span', `status-pill tone-${recordTone(artifact)}`, recordLabel(artifact)),
        el('time', 'mono', humanTime(artifact.at)));
      button.addEventListener('click', () => { state.statementArtifact = artifact.id; renderStatement(); }); list.append(button);
    });
    if (!selected.length) list.append(el('p', 'detail-muted', provided ? '此阶段未运行。' : '此时刻还没有该阶段的结构化记录。'));
    const artifact = selected.find(a => a.id === state.statementArtifact) || selected.find(a => a.kind !== 'operations') || selected[0];
    state.statementArtifact = artifact?.id || null;
    [...list.querySelectorAll('.statement-artifact')].forEach((button, i) => button.classList.toggle('selected', selected[i].id === state.statementArtifact));
    const detail = $('statement-detail'); detail.replaceChildren();
    if (!artifact) {
      detail.append(el('h3', '', provided ? '给定形式声明' : stage?.label || '等待记录'));
      if (provided && state.statementStage === 'source') {
        detail.append(el('p', 'claim-text', data.source_text || ''), el('pre', 'lean-code', data.supplied_statement || '未记录给定声明'));
      } else {
        detail.append(el('p', 'detail-muted', provided ? '本题直接使用给定 Lean 声明，不生成或审核另一份主声明。' : '选择其他步骤查看已有记录。没有记录的步骤保持待处理。'));
      }
      return;
    }
    const record = artifact.data || {}, heading = el('div', 'statement-record-heading');
    heading.append(el('span', `status-pill tone-${recordTone(artifact)}`, recordLabel(artifact)), el('span', 'mono', humanTime(artifact.at, true)));
    detail.append(heading, el('h3', 'mono', artifact.id));
    if (artifact.kind === 'theorems') detail.append(el('p', 'detail-root-notice', '这是带证明占位符的声明编译检查；语义审核与证明完成分别记录。'));
    if (artifact.kind === 'main-reviews') detail.append(el('p', 'detail-root-notice', '原语义审核判定，仅针对下面关联的这一版候选声明。'));
    if (record.reason) detail.append(el('p', 'claim-text', record.reason));
    if (asList(record.differences).length) {
      const differences = el('ul', 'statement-differences'); record.differences.forEach(v => differences.append(el('li', '', display(v)))); detail.append(differences);
    }
    if (record.error_code) detail.append(el('p', 'statement-diagnostics', `原工具错误：${record.error_code}（${record.kind || '未记录类别'}）`));
    if (artifact.kind === 'operations') detail.append(detailJSON(record, '展开原工具执行结果'));
    const source = record.source || record.main_source || record.source_text || record.theorem_source || record.definition_body || record.module_segment;
    if (source) { const part = section('实际记录的声明 / 源码'); part.append(el('pre', 'lean-code', display(source))); detail.append(part); }
    if (record.helper_source) { const part = section('辅助定义'); part.append(el('pre', 'lean-code', record.helper_source)); detail.append(part); }
    const check = record.lean_check || record.machine_gate;
    if (check) { const part = section('Lean 检查', check.ok === true ? '通过' : check.ok === false ? '未通过' : '未记录');
      if (check.diagnostics) part.append(el('pre', 'statement-diagnostics', display(check.diagnostics)));
      part.append(detailJSON(check, '展开检查证据')); detail.append(part); }
    if (record.required_concepts || record.missing || record.candidates) {
      const part = section('库检索与缺口');
      part.append(detailJSON({required_concepts:record.required_concepts, missing:record.missing, candidates:record.candidates}, '展开检索结果 / 缺失概念'));
      part.querySelector('details').open = true; detail.append(part);
    }
    const incoming = records.filter(a => asList(a.relations).some(r => r.id === artifact.id))
      .map(a => ({relation:'被此记录引用', id:a.id}));
    const relations = [...asList(artifact.relations), ...incoming];
    if (relations.length) {
      const part = section('关联候选与前置记录'), buttons = el('div', 'dependency-list');
      relations.forEach(relation => { const related = records.find(a => a.id === relation.id);
        const button = el('button', 'dependency-button', `${relation.id} ↗`); button.disabled = !related;
        button.title = relation.relation; button.addEventListener('click', () => { state.statementStage = related.stage; state.statementArtifact = related.id; renderStatement(); }); buttons.append(button); });
      part.append(buttons); detail.append(part);
    }
    const sourceInfo = section('来源与完整详情'); sourceInfo.append(el('p', 'statement-source mono', artifact.source_path), detailJSON(record, '展开脱敏结构化记录')); detail.append(sourceInfo);
  }

  // Both pages share the same visit-and-return diagram. Only stage names and record labels differ.
  function renderVisitChart(host, stages, visits, {selectedId, onSelect, label, proof=false}) {
    const scrollTop=host.scrollTop, scrollLeft=host.scrollLeft;
    const metrics=ProofTrace.visitChartMetrics(host.clientWidth,stages.length);
    const {width,top,rowHeight,headerHeight,labelX,labelWidth}=metrics,height=top+visits.length*rowHeight+18;
    const axisX=i=>metrics.laneStart+i*metrics.laneGap;
    const chart=svg('svg',{viewBox:`0 0 ${width} ${height}`,width,height,style:`width:${width}px;height:${height}px`,class:'execution-chart',role:'group','aria-label':label,'data-visit-chart':proof?'proof':'statement'});
    const heading=el('div','trace-chart-header');
    const headingChart=svg('svg',{viewBox:`0 0 ${width} ${headerHeight}`,width,height:headerHeight,style:`width:${width}px;height:${headerHeight}px`,class:'execution-chart',role:'group','aria-label':proof?'证明执行阶段':'定理转译阶段'});
    stages.forEach((stage,i)=>{
      chart.append(svg('line',{x1:axisX(i),x2:axisX(i),y1:0,y2:height,class:'trace-lane'}));
      headingChart.append(svg('text',{x:axisX(i),y:27,'text-anchor':'middle',class:'trace-axis'},stage.label));
    });
    heading.append(headingChart);
    let previous=null;
    visits.forEach((visit,i)=>{
      const x=axisX(Math.max(0,stages.findIndex(stage=>stage.id===visit.stage))),y=top+i*rowHeight;
      const back=previous&&x<previous.x;
      if(previous)chart.append(svg('path',{d:`M${previous.x},${previous.y+6} V${y-15} H${x} V${y-6}`,class:`trace-connector${back?' trace-return':''}`}));
      const group=svg('g',{class:`trace-visit tone-${tone(visit.status)}${visit.memory||visit.tool==='memory'?' memory-visit':''}${selectedId===visit.id?' selected':''}`,role:'button',tabindex:0,
        [proof?'data-proof-step':'data-record-id']:visit.id,'aria-label':visit.accessible||`轨迹 ${i+1} ${visit.label} ${visit.statusLabel} ${humanTime(visit.at)}`});
      group.append(svg('rect',{x:0,y:y-23,width,height:60,rx:2,class:'trace-hit'}));
      group.append(svg('text',{x:9,y:y+4,class:'trace-time'},humanTime(visit.at)));
      group.append(visit.memory||visit.tool==='memory'?svg('path',{d:`M${x},${y-6} l6,6 l-6,6 l-6,-6 Z`,class:'trace-point memory-point'}):svg('circle',{cx:x,cy:y,r:5,class:'trace-point'}));
      group.append(svg('text',{x:x+10,y:y+4,class:'trace-ordinal'},String(visit.ordinal||i+1).padStart(2,'0')));
      const target=proof?(visit.node_id==='root'?'◇ root':visit.node_id?'○ '+visit.node_id:'全局'):'';
      const actionLabel=`${back?'↶ ':''}${visit.label}${target?' · '+target:''}`;
      group.append(svg('text',{x:labelX,y:y,class:'trace-action'},ProofTrace.visitLabel(actionLabel,labelWidth)));
      const elapsed=visit.duration_seconds!=null?' · '+visit.duration_seconds.toFixed(1)+'s':'';
      group.append(svg('text',{x:labelX,y:y+23,class:'trace-result'},visit.statusLabel+elapsed));
      const title=svg('title',{});title.textContent=actionLabel+(visit.summary?' — '+visit.summary:'');group.append(title);
      let pressedView=null;
      group.addEventListener('mousedown',event=>{
        pressedView={pageX:window.scrollX,pageY:window.scrollY,listTop:host.scrollTop,listLeft:host.scrollLeft};
        event.preventDefault();
      });
      const open=event=>{
        event?.preventDefault();
        const {pageX,pageY,listTop,listLeft}=pressedView||{pageX:window.scrollX,pageY:window.scrollY,listTop:host.scrollTop,listLeft:host.scrollLeft};
        pressedView=null;
        onSelect(visit);
        const restore=()=>{
          host.scrollTop=listTop;host.scrollLeft=listLeft;
          const key=proof?'data-proof-step':'data-record-id';
          [...host.querySelectorAll('['+key+']')].find(item=>item.getAttribute(key)===visit.id)?.focus({preventScroll:true});
          window.scrollTo({left:pageX,top:pageY,behavior:'instant'});
        };
        restore();requestAnimationFrame(restore);
      };
      group.addEventListener('click',open);group.addEventListener('keydown',event=>{if(['Enter',' '].includes(event.key))open(event);});
      chart.append(group);previous={x,y};
    });
    host.replaceChildren(heading,chart);host.scrollTop=scrollTop;host.scrollLeft=scrollLeft;
  }

  function renderExecutionTrace(data, records) {
    const panel=$('statement-trace-panel'),host=$('statement-trace');panel.hidden=data.mode==='provided';
    const visits=asList(data.trace?.visits).map(visit=>{
      const record=records.find(r=>r.id===visit.id);
      return {...visit,statusLabel:record?.kind==='operations'&&record.data?.phase==='submitted'?'已提交（历史记录）':statusText(visit.status)};
    });
    $('statement-trace-count').textContent=`${visits.length} 次记录 · ${visits.filter(v=>v.return_to_earlier_stage).length} 次返回前序阶段`;
    if(!visits.length){host.replaceChildren(el('p','detail-muted',data.note||'还没有可回放的执行记录。'));return;}
    const names=['输入','检索','定义','候选','编译','审核','锁定'];
    renderVisitChart(host,asList(data.steps).map((stage,i)=>({...stage,label:names[i]})),visits,{selectedId:state.statementArtifact,label:'定理转译实际执行轨迹',onSelect:visit=>{
      state.statementStage=visit.stage;state.statementArtifact=visit.id;renderStatement();
    }});
  }

  function renderProofTrace() {
    const host=$('proof-execution-trace'),detailHost=$('proof-trace-detail'),detail=document.createDocumentFragment();
    const asOf=state.showCurrent?null:state.cursorTime;
    const policy=state.data.current.memory_policy_version??1;
    const rows=ProofTrace.buildSteps(state.events,{asOf,live:state.data.run.live,memoryPolicyVersion:policy,includeLegacyMemory:state.showLegacyMemory});
    const legacy=$('proof-trace-legacy');legacy.hidden=policy>=2;legacy.textContent=state.showLegacyMemory?'折叠旧版自动留存':'显示旧版自动留存';legacy.setAttribute('aria-expanded',String(state.showLegacyMemory));
    $('proof-memory-policy').textContent=policy>=2?'当前策略：由证明 agent 选择保存有价值的经验；事实始终保存，局部证明前缀见对应检查。':'旧版策略：包含原策略逐步自动留存，默认折叠；不是 agent 选择。已证事实始终显示，原检查记录完整保留。';
    $('proof-trace-count').textContent=`${rows.length} 条执行记录（含 ${rows.filter(r=>r.memory).length} 次事实／经验保存） · ${state.showCurrent?'当前全部记录':'截至 '+humanTime(asOf)}`;
    $('proof-trace-earlier').hidden=rows.length<=state.proofLimit;
    const visible=rows.slice(-state.proofLimit);
    if(!visible.length){host.replaceChildren(el('p','detail-muted',state.data.current.proof_started===false?'尚未开始构造 DAG；主声明转译过程在 01。':'本运行尚无原始证明工具调用记录。'));if(state.proofDetailMode==='node')renderNodeDetail(detail);detailHost.replaceChildren(detail);return;}
    state.proofSelection=ProofTrace.selectedStep(visible,{selection:state.proofSelection,follow:state.follow,current:state.showCurrent,detailMode:state.proofDetailMode});
    const visits=visible.map(row=>({...row,statusLabel:row.memory?'已保存':statusText(row.status),accessible:`证明轨迹 ${row.ordinal} ${row.label} ${row.node_id||'全局'} ${row.memory?'已保存':statusText(row.status)}`}));
    renderVisitChart(host,ProofTrace.stages,visits,{selectedId:state.proofSelection,proof:true,label:'自然语言证明转译实际执行轨迹',onSelect:row=>{
      state.proofSelection=row.id;state.proofDetailMode='step';if(row.node_id)state.selected=row.node_id;
      // Inspect this record without rewinding the graph or truncating the trace.
      state.follow=false;
      renderFrame();renderSnapshotControl();
    }});
    if(state.proofDetailMode==='node'){
      const back=el('button','quiet-button','← 返回所选操作');back.addEventListener('click',()=>{state.proofDetailMode='step';renderProofTrace();});detail.append(back);
      renderNodeDetail(detail);detailHost.replaceChildren(detail);return;
    }
    const selected=visible.find(r=>r.id===state.proofSelection);if(!selected){detailHost.replaceChildren(detail);return;}
    const latestSelected=selected.id===rows.at(-1)?.id;
    detail.append(el('span','eyebrow',`${latestSelected?(state.showCurrent?(state.data.run.live?'最新步骤记录':'最终步骤记录'):'所选时刻的最后一步'):'所选历史步骤'} · STEP ${selected.ordinal} / ${selected.memory?'已保存':statusText(selected.status)}`),el('h3','',selected.label),el('p','proof-trace-target','目标：'+(selected.node_id||'全局证明流程')),
      el('p','claim-text',selected.diagnostics&&selected.summary===String(selected.diagnostics)?'':selected.summary));
    const rewind=el('button','dependency-button','回到这一步的时间 ↶');rewind.addEventListener('click',()=>seekTime(selected.at));detail.append(rewind);
    if(!latestSelected){const newest=el('button','dependency-button','返回最新步骤 ↗');newest.addEventListener('click',attachCurrent);detail.append(newest);}
    const timing=el('dl','proof-trace-times');
    const times=selected.tool==='memory'?[['保存确认',humanTime(selected.completed_at,true)],['时间依据','对应工具完成；未单独计时']]:[['开始',selected.started_at?humanTime(selected.started_at,true):'原记录未给出起点'],['结束',selected.completed_at?humanTime(selected.completed_at,true):'未记录结束'],[selected.tool==='compression'?'压缩耗时':'工具耗时',selected.duration_seconds!=null?selected.duration_seconds.toFixed(2)+' 秒':'未记录']];
    for(const [name,value]of times){timing.append(el('dt','',name),el('dd','mono',value));}
    detail.append(timing);
    if(selected.memory){
      const memory=selected.memory;
      const section=(title,text,code=false)=>{const block=el(code?'details':'section','memory-detail-section');block.append(el(code?'summary':'h4','',title),el(code?'pre':'p',code?'lean-code':'claim-text',text));detail.append(block);};
      if(memory.experience){
        section(({success:'成功经验',failure:'失败经验',mixed:'恢复／综合经验'})[memory.experience.outcome]||'经验',memory.experience.lesson);
        section('保存方式',memory.experience.selected_by==='legacy_automatic'?'旧版策略自动留存':'证明 agent 主动选择');
        if(memory.experience.why_now)section('为什么现在保存',memory.experience.why_now);
        if(memory.experience.evidence_ids?.length)section('实际检查依据',memory.experience.evidence_ids.join('、'));
        if(memory.experience.supersedes)section('修订来源',memory.experience.supersedes+(memory.experience.revision?' · 第 '+memory.experience.revision+' 版':''));
        if(memory.experience.prior_evidence_ids?.length)section('合并前保留的依据',memory.experience.prior_evidence_ids.join('、'));
        if(memory.experience.action)section('对应动作',memory.experience.action,true);
        if(memory.experience.next_action)section('保存时返回的后续建议',memory.experience.next_action);
        detail.append(el('p','detail-muted',memory.experience.meaning));
      }
      if(memory.fact){
        section('已证事实 · '+memory.fact.node_id,memory.fact.claim||'该辅助引理的精确声明与证明文件已保存，可供后续节点使用。');
        if(memory.fact.statement)section('查看保存的 Lean 声明',memory.fact.statement,true);
        section('查看精确类型',memory.fact.elaborated_type,true);
        if(memory.fact.body)section('查看保存的证明',memory.fact.body,true);
      }
      if(memory.step){
        section('保留的成功证明前缀',memory.step.prefix||'空前缀',true);
        detail.append(el('p','detail-muted',`${memory.step.open_goal_count} 个剩余局部目标；局部检查与完整证明认证分开记录。`));
      }
      const sourceIds=selected.source_step_ids||[selected.source_step_id];
      for(const sourceId of sourceIds.filter(id=>id&&rows.some(r=>r.id===id))){
      const source=el('button','dependency-button','查看对应检查 '+(sourceIds.length>1?sourceId.slice(0,8)+' ':'')+'↗');source.addEventListener('click',()=>{
        const sourceIndex=rows.findIndex(r=>r.id===sourceId);
        if(sourceIndex>=0)state.proofLimit=Math.max(state.proofLimit,rows.length-sourceIndex);
        state.proofSelection=sourceId;state.proofDetailMode='step';state.follow=false;renderProofTrace();
        const target=[...host.querySelectorAll('[data-proof-step]')].find(item=>item.getAttribute('data-proof-step')===sourceId);
        if(target)host.scrollTop+=target.getBoundingClientRect().top-host.getBoundingClientRect().top-42;
      });detail.append(source);}
      detail.append(el('p','detail-muted',selected.tool==='save_experience'?'这是原 save_experience 调用的真实结果；经验选择不等于新的数学认证。':'此节点展开原工具的保存结果，不是额外模型调用。时间取原工具完成记录。'));
    }
    const selectedRecord=state.events.find(e=>e._source_key===(selected.end_key||selected.start_key));
    const compactionResult=selectedRecord?.details?.result;
    if(selected.tool==='prepare_compaction'&&compactionResult?.ok===true){
      detail.append(el('p','detail-muted','本步由证明 agent 判断经验价值；可以不新增经验。整理完成不等于压缩已完成，后续压缩有独立记录。'));
    }
    if(selected.tool==='request_compaction')detail.append(el('p','detail-muted','申请只触发安全边界交接；先整理经验，再压缩，不增加数学证明进度。'));
    const node=state.frame.nodes.find(n=>String(n.id)===String(selected.node_id));
    if(node){const inspect=el('button','dependency-button',`查看 ${selected.node_id} 的命题、代码与依赖 ↗`);inspect.addEventListener('click',()=>selectNode(String(selected.node_id)));detail.append(inspect);}
    const context=asList(state.frame.contexts).find(c=>c.id===(selected.node_id==='root'?'main':selected.context_id));
    if(context?.has_records){const open=el('button','dependency-button',selected.node_id==='root'?'进入 01 · 主声明转译轨迹 ↗':'进入 01 · 此节点的定理转译轨迹 ↗');open.addEventListener('click',()=>switchView('statement',context.id));detail.append(open,el('p','detail-muted',selected.node_id==='root'?'主声明锁定后进入此证明流程；声明审核与证明通过分开记录。':`DAG ${selected.node_id} → 该节点的定理转译 → 返回同一节点；声明审核不替代证明通过。`));}
    else if(selected.tool==='review_node')detail.append(el('p','detail-muted','此时尚无可显示的节点声明转译产物；不会借用主定理的记录。'));
    if(selected.diagnostics&&tone(selected.status)==='failed')detail.append(el('pre','proof-trace-diagnostic',selected.diagnostics));
    const record=state.events.find(e=>e._source_key===(selected.end_key||selected.start_key));
    if(record)detail.append(detailJSON(selected.memory||selected.tool==='compression'?selected.record_details:record.details,selected.tool==='compression'?'查看本步压缩元数据':selected.memory?'查看保存依据与原调用关联':'查看本步原始操作 / 检查结果'));
    detailHost.replaceChildren(detail);
  }

  function layoutGraph(nodes) {
    const unique = [...new Map(nodes.filter(node => node.id != null).map(node => [nodeId(node), node])).values()];
    const map = new Map(unique.map(node => [nodeId(node), { ...node, x: 0, y: 0, level: 0 }]));
    const ids = [...map.keys()].sort((a, b) => a.localeCompare(b, 'en'));
    const root = ids.find(id => isRoot(map.get(id)));
    const parents = new Map(ids.map(id => [id, new Set()]));
    const children = new Map(ids.map(id => [id, new Set()]));
    ids.forEach(id => dependencies(map.get(id)).forEach(dep => {
      if (!map.has(dep)) return;
      children.get(id).add(dep); parents.get(dep).add(id);
    }));
    // A helper can belong to this proof before its root dependency is recorded.
    // Attach such branches for placement only; source depends_on stays intact.
    if (root != null) ids.forEach(id => {
      if (id !== root && !parents.get(id).size) {
        parents.get(id).add(root); children.get(root).add(id);
      }
    });
    const remaining = new Map(ids.map(id => [id, parents.get(id).size]));
    const queue = ids.filter(id => !remaining.get(id)), seen = new Set();
    for (let index = 0; index < queue.length; index++) {
      const id = queue[index]; seen.add(id);
      [...children.get(id)].sort().forEach(child => {
        map.get(child).level = Math.max(map.get(child).level, map.get(id).level + 1);
        remaining.set(child, remaining.get(child) - 1);
        if (!remaining.get(child)) queue.push(child);
      });
    }
    const cycle = seen.size !== map.size;
    if (cycle) {
      const last = Math.max(0, ...[...map.values()].map(node => node.level)) + 1;
      ids.filter(id => !seen.has(id)).forEach(id => { map.get(id).level = id === root ? 0 : last; });
    }
    const treeChildren = new Map(ids.map(id => [id, []])), primaryParent = new Map();
    ids.forEach(id => {
      if (id === root) return;
      // Longest dependency depth keeps shared premises below all their users.
      // Pick one deterministic tree parent and keep other real edges visible.
      const choices = [...parents.get(id)].filter(parent => map.get(parent).level < map.get(id).level)
        .sort((a, b) => map.get(b).level - map.get(a).level || a.localeCompare(b, 'en'));
      const parent = choices[0] ?? root;
      if (parent != null && parent !== id) {
        primaryParent.set(id, parent); treeChildren.get(parent).push(id);
      }
    });
    const roots = ids.filter(id => !primaryParent.has(id));
    roots.sort((a, b) => Number(b === root) - Number(a === root) || a.localeCompare(b, 'en'));
    const widths = new Map(), gap = 30, row = H + 36;
    function measure(id) {
      const branches = treeChildren.get(id);
      const width = Math.max(W, branches.reduce((sum, child) => sum + measure(child), 0) + Math.max(0, branches.length - 1) * gap);
      widths.set(id, width); return width;
    }
    function place(id, left, depth) {
      const node = map.get(id), branches = treeChildren.get(id);
      node.x = left + (widths.get(id) - W) / 2; node.y = depth * row;
      node.level = depth;
      let next = left;
      branches.forEach(child => { place(child, next, depth + 1); next += widths.get(child) + gap; });
    }
    let next = 0;
    roots.forEach(id => { measure(id); place(id, next, 0); next += widths.get(id) + gap; });
    const positioned = [...map.values()];
    const associations = [...primaryParent].filter(([id, parent]) => !dependencies(map.get(parent)).includes(id))
      .map(([child, parent]) => ({ child, parent }));
    return { nodes: positioned, map, primaryParent, associations, cycle,
      bounds: { x: 0, y: 0, width: Math.max(W, next - gap), height: Math.max(H, ...positioned.map(node => node.y + H)) } };
  }
  function graphNodeStatus(node) {
    return ProofTrace.graphStatus(node,{current:state.showCurrent,live:state.data?.run.live===true,runStatus:state.data?.current.status??state.data?.run.status});
  }

  function renderGraph() {
    const world = $('graph-world'); world.replaceChildren();
    const previousBounds = state.layout?.bounds;
    state.layout = layoutGraph(state.frame.nodes);
    if (!state.manualTransform && (!previousBounds || previousBounds.width !== state.layout.bounds.width
        || previousBounds.height !== state.layout.bounds.height)) state.needsFit = true;
    const { nodes, map, cycle, primaryParent, associations } = state.layout;
    $('graph-empty').hidden = nodes.length > 0;
    if (!nodes.length) {
      $('graph-empty').querySelector('h3').textContent = '此时刻尚无已记录节点';
      $('graph-empty').querySelector('p').textContent = '向后回放以查看节点的出现。当前快照可通过右下方按钮单独查看。';
    }
    const warnings = [];
    if (cycle) warnings.push('源数据含循环依赖；已原样保留连接，请查看节点记录。');
    if (state.showCurrent && hasOperation()) warnings.push(`观测活动：${operationText(state.data.current.active_operation)}`);
    const activeNodes=nodes.filter(node=>graphNodeStatus(node)==='in_progress');
    if(activeNodes.length)warnings.push('当前节点：'+activeNodes.map(node=>node.id).join('、'));
    $('graph-warning').hidden = !warnings.length;
    $('graph-warning').textContent = warnings.join('  ·  ');
    const edges = svg('g', { class: 'graph-edges' });
    associations.forEach(({ child, parent }) => {
      const lower = map.get(child), upper = map.get(parent);
      const x1 = upper.x + W / 2, y1 = upper.y + H, x2 = lower.x + W / 2, y2 = lower.y;
      const bend = (y2 - y1) / 2;
      const path = svg('path', { d: `M${x1},${y1} C${x1},${y1 + bend} ${x2},${y2 - bend} ${x2},${y2}`,
        class: 'tree-association', 'data-layout-parent': parent, 'data-layout-child': child });
      path.append(svg('title', {}, `${parent} / ${child} · 辅助目标布局归属；未记录为证明依赖`));
      edges.append(path);
    });
    nodes.forEach(node => {
      dependencies(node).forEach(id => {
        const source = map.get(id);
        if (!source) return;
        const x1 = source.x + W / 2, y1 = source.y, x2 = node.x + W / 2, y2 = node.y + H;
        const bend = Math.max(22, Math.abs(y1 - y2) * .5);
        const bodyReference = node.dependency_evidence?.[id] === 'body_reference';
        const shared = primaryParent.get(id) !== nodeId(node);
        const path = svg('path', { d: `M${x1},${y1} C${x1},${y1 - bend} ${x2},${y2 + bend} ${x2},${y2}`,
          class: `graph-edge${shared ? ' shared-dependency' : ''}${bodyReference ? ' body-reference' : ''}${state.selected === id || state.selected === nodeId(node) ? ' selected' : ''}` });
        path.append(svg('title', {}, `${id} → ${nodeId(node)}${bodyReference ? ' · Lean 正文文本引用，非 Kernel 依赖认证' : ' · 源计划 / state 依赖'}`)); edges.append(path);
      });
    });
    world.append(edges);
    nodes.forEach(node => {
      const id = nodeId(node), root = isRoot(node), displayStatus=graphNodeStatus(node);
      const group = svg('g', { class: `graph-node tone-${tone(displayStatus)}${root ? ' root' : ''}${state.selected === id ? ' selected' : ''}`,
        transform: `translate(${node.x} ${node.y})`, tabindex: '0', role: 'button', 'data-node-id': id, 'data-node-status': displayStatus, 'aria-label': `${root ? '最终目标' : '节点'} ${id}，${statusText(displayStatus)}。${nodeClaim(node)}` });
      group.append(svg('title', {}, `${id} · ${statusText(displayStatus)}\n${nodeClaim(node)}`));
      group.append(svg('rect', { class: 'node-shell', width: W, height: H }));
      group.append(svg('rect', { class: 'node-accent', x: 0, y: 16, width: 3, height: 21 }));
      group.append(svg('text', { class: 'node-key', x: 14, y: 24 }, id.length > 15 ? `${id.slice(0, 14)}…` : id));
      group.append(svg('text', { class: 'node-state', x: W - 13, y: 24, 'text-anchor': 'end' }, statusText(displayStatus)));
      const foreign = svg('foreignObject', { x: 14, y: 37, width: W - 28, height: 47 });
      const claim = document.createElementNS('http://www.w3.org/1999/xhtml', 'div');
      claim.setAttribute('class', 'svg-claim'); claim.textContent = nodeClaim(node); foreign.append(claim); group.append(foreign);
      group.append(svg('line', { x1: 14, x2: W - 14, y1: 91, y2: 91, stroke: '#465a45', 'stroke-width': '.6' }));
      group.append(svg('text', { class: 'node-meta', x: 14, y: 105 }, `${dependencies(node).length} DEPS${node.statement ? '  /  LEAN' : ''}`));
      if (root) group.append(svg('text', { class: 'node-root-label', x: W - 13, y: 105, 'text-anchor': 'end' }, '◇ 最终目标'));
      group.addEventListener('click', event => { event.stopPropagation(); selectNode(id); });
      group.addEventListener('keydown', event => {
        if (event.key === 'Enter' || event.key === ' ') { event.preventDefault(); selectNode(id); }
      });
      world.append(group);
    });
    if (state.needsFit && nodes.length) {
      requestAnimationFrame(() => { fitGraph(); state.needsFit = false; });
    } else transformGraph();
  }
  function operationText(operation) {
    if (typeof operation !== 'object') return String(operation);
    const activity = display(operation.label ?? operation.title ?? operation.activity ?? operation.kind ?? operation.step ?? operation);
    return `${operation.layer ? `${operation.layer} / ` : ''}${activity}${operation.fresh === false ? ' · 监视记录已过期' : ''}`;
  }
  function hasOperation() {
    const operation = state.data?.current.active_operation;
    return !!state.data?.run.live && !!operation && (typeof operation !== 'object'
      || ['activity', 'label', 'title', 'kind', 'step', 'tool'].some(key => operation[key] != null));
  }
  function transformGraph() {
    const { x, y, scale } = state.transform;
    $('graph-world').setAttribute('transform', `translate(${x} ${y}) scale(${scale})`);
    $('zoom-value').textContent = `${Math.round(scale * 100)}%`;
  }
  function fitGraph() {
    if (!state.layout?.nodes.length) return;
    const rect = $('graph').getBoundingClientRect(), b = state.layout.bounds;
    const scale = Math.max(.12, Math.min(1.15, (rect.width - 48) / b.width, (rect.height - 64) / b.height));
    state.transform = { scale, x: (rect.width - b.width * scale) / 2 - b.x * scale,
      y: 42 - b.y * scale };
    state.manualTransform = false; transformGraph();
  }
  function zoom(factor, cx, cy) {
    const rect = $('graph').getBoundingClientRect();
    cx ??= rect.width / 2; cy ??= rect.height / 2;
    const old = state.transform, scale = Math.max(.12, Math.min(3, old.scale * factor));
    state.transform = { x: cx - (cx - old.x) * scale / old.scale, y: cy - (cy - old.y) * scale / old.scale, scale };
    state.manualTransform = true; transformGraph();
  }
  function selectNode(id) {
    const graphHadFocus = document.activeElement?.closest?.('.graph-node');
    state.selected = id; state.statementContext = id === 'root' ? 'main' : 'node:' + id;
    updateLocation(); state.proofDetailMode='node'; renderGraph();renderProofTrace();$('proof-trace-detail').scrollIntoView({block:'nearest',behavior:'smooth'});
    if (graphHadFocus) [...document.querySelectorAll('.graph-node')].find(node => node.dataset.nodeId === id)?.focus({ preventScroll: true });
  }
  function section(title, secondary = '') {
    const node = el('section', 'detail-section'), heading = el('h3', '', title);
    if (secondary) heading.append(el('span', '', secondary));
    node.append(heading); return node;
  }
  function detailJSON(value, label = '展开原始详情') {
    const details = el('details', 'detail-disclosure');
    details.append(el('summary', '', label), el('pre', 'detail-json', typeof value === 'string' ? value : JSON.stringify(value ?? {}, null, 2)));
    return details;
  }
  function renderNodeDetail(host=$('proof-trace-detail')) {
    const node = state.frame.nodes.find(item => nodeId(item) === state.selected);
    if (!node) {
      const empty = el('div', 'inspector-empty');
      empty.append(el('h3', '', state.selected ? `${state.selected} 尚未出现在此帧` : '沿依赖阅读证明'),
        el('p', '', '点选图中节点，可查看该时刻记录的自然语言主张、Lean 代码和依赖。'));
      host.append(empty);return;
    }
    const displayStatus=graphNodeStatus(node);
    const kicker = el('div', 'detail-kicker');
    kicker.append(el('span', '', isRoot(node) ? '最终目标 / ROOT' : '局部命题 / LOCAL CLAIM'), el('span', `status-pill tone-${tone(displayStatus)}`, statusText(displayStatus)));
    host.append(kicker, el('h3', 'detail-node-id', nodeId(node)));
    if (isRoot(node)) host.append(el('p', 'detail-root-notice', '最终目标的状态独立记录。辅助节点全部证明、局部 goals 清零，均不替代根候选验证及后续流水线检查。'));
    const claim = section('自然语言主张', 'NATURAL LANGUAGE'); claim.append(el('p', 'claim-text', nodeClaim(node))); host.append(claim);
    const contextId = isRoot(node) ? 'main' : 'node:' + nodeId(node);
    const translation = asList(state.frame.contexts).find(c => c.id === contextId);
    if (translation) {
      const localOnly=statementContextMode(translation)==='local';
      const part = section(localOnly?'局部声明检查':'定理转译 / 声明审核', localOnly?'本次无独立转译调用':translation.kind === 'helper' ? '本 DAG 节点的独立记录' : '主定理与根目标');
      const button = el('button', 'translation-link', translation.data?.mode === 'provided' ? '查看给定声明 ↗' : localOnly?'查看本节点声明与检查方式 ↗':'进入此节点的定理转译轨迹 ↗');
      button.addEventListener('click', () => { state.statementStage=null;state.statementArtifact=null;switchView('statement',contextId); });
      part.append(button,el('p','detail-muted',translation.data?.note || '按原记录关联，审核通过与证明完成分别显示。'));host.append(part);
    }
    const deps = section('依赖', `${dependencies(node).length} DEPENDENCIES`), depList = el('div', 'dependency-list');
    dependencies(node).forEach(id => {
      const exists = state.frame.nodes.some(item => nodeId(item) === id);
      const bodyReference = node.dependency_evidence?.[id] === 'body_reference';
      const button = el('button', `dependency-button${bodyReference ? ' body-reference' : ''}`, exists ? `${id}${bodyReference ? ' ↗' : ''}` : `${id} · 此帧未记录`);
      button.title = bodyReference ? 'Lean 正文文本引用，非 Kernel 依赖认证' : '源计划 / state 依赖';
      button.disabled = !exists; button.addEventListener('click', () => selectNode(id)); depList.append(button);
    });
    deps.append(dependencies(node).length ? depList : el('p', 'detail-muted', '此帧未记录前置依赖。')); host.append(deps);
    if (dependencies(node).some(id => node.dependency_evidence?.[id] === 'body_reference')) deps.append(el('p', 'detail-root-notice', '虚线边由 Lean 正文中的名字引用识别，仅表示文本引用，非 Kernel 依赖认证。'));
    const code = section('Lean 代码', 'RECORDED SOURCE'), header = el('div', 'code-header'), tabs = el('div', 'code-tabs');
    ['statement', 'body'].forEach(tab => {
      const button = el('button', state.codeTab === tab ? 'active' : '', tab);
      button.addEventListener('click', () => { state.codeTab = tab; renderProofTrace(); }); tabs.append(button);
    });
    const content = node[state.codeTab], copy = el('button', 'copy-button', '复制'); copy.disabled = !content;
    copy.addEventListener('click', async () => {
      try { await navigator.clipboard.writeText(String(content)); copy.textContent = '已复制'; }
      catch { notice('浏览器未允许复制，请在代码区选择并复制文本。'); }
    });
    header.append(tabs, copy); code.append(header, content ? el('pre', 'lean-code', content) : el('p', 'detail-muted', `此帧未记录 Lean ${state.codeTab}。`)); host.append(code);

  }

  function compressionCount(events) {
    const ids = new Set();
    const hasStarts = state.events.some(event => /(?:compress|compact).*\.started$/i.test(String(event.kind)));
    events.filter(event => /compress|compact/i.test(String(event.kind))).forEach(event => {
      const sourceId = String(event._source_key ?? '').match(/^compression:(\d+):/);
      const started = event.details && typeof event.details === 'object' ? event.details.started_at : null;
      if (sourceId) ids.add(`source:${sourceId[1]}`);
      else if (started) ids.add(`at:${started}`);
      else if (!hasStarts || !/\.completed$/i.test(String(event.kind))) ids.add(`event:${event.seq}`);
    });
    return ids.size;
  }
  function renderSnapshotControl() {
    $('follow-live').disabled=!state.data;
    $('follow-live').classList.toggle('following',state.follow);
    $('follow-live').textContent=state.follow?'● 已附着实时':state.showCurrent&&state.data?.run.live?'返回最新步骤 ↗':state.data?.run.live?'返回当前快照 ↗':'查看最终快照 ↗';
    $('unread-events').hidden=!state.unread;$('unread-events').textContent=`+${state.unread} 条新事件`;
    renderTimeHistory();
  }
  function localDateTime(ms) {
    const d=new Date(ms),pad=n=>String(n).padStart(2,'0');
    return `${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())}T${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
  }
  function renderTimeHistory() {
    if(!state.data)return;
    const entries=ProofTrace.historyEntries(state.events,{view:state.view,context:state.statementContext});
    const range=$('history-range'),input=$('history-time');
    $('time-history').hidden=!entries.length;if(!entries.length)return;
    const first=entries[0].at,last=entries.at(-1).at,at=state.showCurrent?last:state.cursorTime;
    range.min=first;range.max=Math.max(first+1,last);range.value=Math.max(first,Math.min(last,at));
    range.setAttribute('aria-valuetext',humanTime(at,true));range.disabled=first===last;
    input.min=localDateTime(first);input.max=localDateTime(last);
    if(document.activeElement!==input)input.value=localDateTime(at);
    $('history-start').textContent=humanTime(first,true);$('history-end').textContent=humanTime(last,true);
    $('history-mode').textContent=state.showCurrent?(state.data.run.live?'当前实时':'最终快照'):'正在查看历史';
    $('time-history').classList.toggle('is-historical',!state.showCurrent);
    $('history-current-time').textContent=humanTime(at,true);
    $('history-prev').disabled=!entries.some(e=>e.at<at);
    $('history-next').disabled=state.showCurrent||!entries.some(e=>e.at>at);
    const record=[...entries].reverse().find(e=>e.at<=at);
    const recordLabel=String(record?.label||'').replace(/[A-Za-z][A-Za-z_]+/g,word=>statusNames[word]||word);
    $('history-record').textContent=state.showCurrent?`共 ${entries.length} 个时刻 · ${state.view==='dag'?'从开始构造 DAG 计时':'当前转译对象'}`:record?`最近记录：${recordLabel}`:'此时尚无该阶段记录';
    $('history-record').title=$('history-record').textContent;
    $('history-latest').textContent=state.data.run.live?'返回最新':'返回最终快照';
    $('history-latest').disabled=state.showCurrent;
    $('history-kind').textContent=state.showCurrent?'当前全部执行记录':'历史截面 · '+humanTime(at,true);
  }
  function seekTime(at) {
    if(!state.data||parseTime(at)==null)return;
    state.follow=false;state.showCurrent=false;state.cursorTime=parseTime(at);
    state.cursorIndex=ProofTrace.indexAtTime(state.events,state.cursorTime);
    state.proofSelection=null;state.proofDetailMode='step';state.statementArtifact=null;state.statementStage=null;
    state.needsFit=!state.manualTransform;
    updateLocation();renderFrame();renderSnapshotControl();
  }
  function seekEvent(index) {const event=state.events[index];if(event)seekTime(event.at);}
  function stepHistory(direction) {
    const entries=ProofTrace.historyEntries(state.events,{view:state.view,context:state.statementContext});
    const at=state.showCurrent?entries.at(-1)?.at:state.cursorTime;
    const next=direction<0?[...entries].reverse().find(e=>e.at<at):entries.find(e=>e.at>at);
    if(next)seekTime(next.at);
  }
  function attachCurrent() {
    if(!state.data)return;
    state.cursorTime=null;state.follow=!!state.data.run.live;state.showCurrent=true;state.unread=0;state.cursorIndex=state.events.length-1;
    state.proofSelection=null;state.proofDetailMode='step';
    updateLocation();renderFrame();renderSnapshotControl();
  }

  $('history-prev').addEventListener('click',()=>stepHistory(-1));
  $('history-next').addEventListener('click',()=>stepHistory(1));
  $('history-latest').addEventListener('click',attachCurrent);
  let historySeekFrame=null,historySeekValue=null;
  $('history-range').addEventListener('input',event=>{historySeekValue=Number(event.target.value);if(historySeekFrame!=null)return;historySeekFrame=requestAnimationFrame(()=>{historySeekFrame=null;seekTime(historySeekValue);});});
  $('history-time').addEventListener('change',event=>{const at=Date.parse(event.target.value);if(Number.isFinite(at))seekTime(at);});
  $('proof-trace-earlier').addEventListener('click',()=>{state.proofLimit+=100;renderProofTrace();});
  $('proof-trace-legacy').addEventListener('click',()=>{state.showLegacyMemory=!state.showLegacyMemory;renderProofTrace();});
  $('show-proof-trace').addEventListener('click',()=>$('dag-trace-panel').scrollIntoView({block:'start',behavior:'smooth'}));
  $('run-select').addEventListener('change', event => loadRun(event.target.value, {history:'push'}));
  $('refresh-runs').addEventListener('click', loadRuns);
  $('zoom-in').addEventListener('click', () => zoom(1.2));
  $('zoom-out').addEventListener('click', () => zoom(1 / 1.2));
  $('fit-graph').addEventListener('click', fitGraph);
  $('follow-live').addEventListener('click', attachCurrent);
  $('graph').addEventListener('wheel', event => {
    event.preventDefault(); const rect = $('graph').getBoundingClientRect();
    zoom(Math.exp(-event.deltaY * .0014), event.clientX - rect.left, event.clientY - rect.top);
  }, { passive: false });
  $('graph').addEventListener('pointerdown', event => {
    if (event.button !== 0 || event.target.closest('.graph-node')) return;
    state.dragging = { id: event.pointerId, x: event.clientX, y: event.clientY, tx: state.transform.x, ty: state.transform.y };
    $('graph').setPointerCapture(event.pointerId); $('graph').classList.add('panning');
  });
  $('graph').addEventListener('pointermove', event => {
    const drag = state.dragging;
    if (!drag || drag.id !== event.pointerId) return;
    state.transform.x = drag.tx + event.clientX - drag.x; state.transform.y = drag.ty + event.clientY - drag.y;
    state.manualTransform = true; transformGraph();
  });
  const endDrag = () => { state.dragging = null; $('graph').classList.remove('panning'); };
  $('graph').addEventListener('pointerup', endDrag); $('graph').addEventListener('pointercancel', endDrag);
  $('graph').addEventListener('keydown', event => {
    if (event.target.closest('.graph-node')) return;
    if (event.key === 'Home') { event.preventDefault(); fitGraph(); }
    else if (event.key === '+' || event.key === '=') { event.preventDefault(); zoom(1.2); }
    else if (event.key === '-') { event.preventDefault(); zoom(1 / 1.2); }
    else if (['ArrowLeft', 'ArrowRight', 'ArrowUp', 'ArrowDown'].includes(event.key)) {
      event.preventDefault(); state.manualTransform = true;
      state.transform.x += event.key === 'ArrowLeft' ? 35 : event.key === 'ArrowRight' ? -35 : 0;
      state.transform.y += event.key === 'ArrowUp' ? 35 : event.key === 'ArrowDown' ? -35 : 0; transformGraph();
    }
  });
  new ResizeObserver(() => {
    if (state.data) {
      
      if (!state.manualTransform && !document.querySelector('.workspace').hidden) { state.needsFit = true; renderGraph(); }
    }
  }).observe($('graph-surface'));
  const visitWidths=new Map();let visitResizeQueued=false;
  const visitResizeObserver=new ResizeObserver(entries=>{
    let changed=false;
    for(const entry of entries){
      const width=entry.target.clientWidth;
      if(width>0&&visitWidths.get(entry.target.id)!==width){visitWidths.set(entry.target.id,width);changed=true;}
    }
    if(!changed||!state.data||visitResizeQueued)return;
    visitResizeQueued=true;
    requestAnimationFrame(()=>{
      visitResizeQueued=false;
      if(!state.data)return;
      if(state.view==='dag')renderProofTrace();else renderStatement();
    });
  });
  visitResizeObserver.observe($('proof-execution-trace'));visitResizeObserver.observe($('statement-trace'));
  window.addEventListener('beforeunload', () => { state.stream?.close(); state.controller?.abort(); });
  $('final-code-panel').addEventListener('toggle',()=>{if($('final-code-panel').open&&!state.finalCode&&!state.finalCodeController)loadFinalCode();});
  $('final-code-copy').addEventListener('click',async()=>{
    const file=state.finalCode?.files.find(f=>f.name===state.finalCodeFile);if(!file)return;
    try{await navigator.clipboard.writeText(file.content);$('final-code-copy').textContent='已复制';setTimeout(()=>{$('final-code-copy').textContent='复制当前文件';},1500);}
    catch(error){$('final-code-note').textContent='复制未完成，可选中源码手动复制。';}
  });
  $('statement-toggle').addEventListener('click', () => { state.statementExpanded = !state.statementExpanded; renderStatement(); });
  $('view-statement').addEventListener('click', () => switchView('statement', 'main'));
  $('view-dag').addEventListener('click', () => switchView('dag'));
  $('statement-back-to-dag').addEventListener('click', () => switchView('dag'));
  $('statement-context-select').addEventListener('change', event => {
    state.statementStage=null;state.statementArtifact=null;switchView('statement',event.target.value);
  });
  window.addEventListener('popstate', () => {
    const params=new URL(location.href).searchParams;
    const id=params.get('id');
    if(id && id!==state.data?.run.id) loadRun(id,{view:params.get('view')||'dag',context:params.get('context')||'main',history:false});
    else if(state.data){state.view=params.get('view')||'dag';state.statementContext=params.get('context')||'main';const at=parseTime(params.get('at'));if(at!=null)seekTime(at);else attachCurrent();}
  });
  loadRuns();
})();
