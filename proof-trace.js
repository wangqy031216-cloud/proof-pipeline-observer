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
