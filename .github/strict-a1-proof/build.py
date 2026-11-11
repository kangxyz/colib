#!/usr/bin/env python3
"""Direct Lean proof validation of one frozen source DAG. No kernel replay."""
from common import *
import concurrent.futures,tarfile,time,tomllib,sys
CANDIDATES=set(PLAN['candidate_modules'])
def options(m):return package_options(m)
PRIOR_PRODUCT_FINGERPRINTS={}
DEPENDENCY_PRODUCT_IDENTITIES={}
def dependency_product_identity(m):
 if m not in DEPENDENCY_PRODUCT_IDENTITIES:DEPENDENCY_PRODUCT_IDENTITIES[m]=product_fingerprint(record(m,'dependency-identity-only')['products'])
 return DEPENDENCY_PRODUCT_IDENTITIES[m]
def initialize():
 require((ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0','Wrong toolchain')
 pins={e['name']:e['rev'] for e in json.loads((ROOT/'lake-manifest.json').read_text())['packages']}
 for package,pin in [('mathlib',PINS['mathlib_revision']),('Stacks',PINS['stacks_revision'])]:
  require(pins[package]==pin,'Wrong resolved pin')
  actual=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/package),'rev-parse','HEAD'],text=True).strip();require(actual==pin,'Wrong package HEAD')
  dirty=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/package),'status','--porcelain','--untracked-files=no'],text=True);require(not dirty.strip(),'Dirty dependency source')
 version=subprocess.check_output(['lean','--version'],text=True).strip();require(PINS['lean_commit'] in version and '4.35.0' in version,'Wrong Lean compiler')
 leanpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip();roots=[str((ROOT/p).resolve()) if not Path(p).is_absolute() else p for p in leanpath.split(os.pathsep) if p]
 prefix=subprocess.check_output(['lean','--print-prefix'],text=True).strip();roots.append(str(Path(prefix)/'lib/lean'))
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(roots))
 for key in list(env):
  if any(word in key.upper() for word in ('TOKEN','SECRET','PASSWORD','CREDENTIAL')):env.pop(key)
 restored=json.loads((OUT/'restored.json').read_text());reused={};missing=[];external=set()
 for m,e in NODES.items():
  require(sha(source(m))==e['source_sha256'] and imports(source(m))==e['source_imports'],'Frozen source changed: '+m)
  external.update(d for d in e['source_imports'] if d not in NODES)
  if m in CANDIDATES and m not in restored:continue
  if m not in restored and owner(m)!='Stacks':continue
  try:
   _,di=bundle(m)
   provenance=restored.get(m,{'provenance':'official-pinned-stacks-checkpoint-733969670'})
   require(provenance.get('source_sha256',e['source_sha256'])==e['source_sha256'],'Cached source identity differs')
   if m in OVERLAY['force_package_revalidation'] or m in OVERLAY['prior_partial_product_change_potential_revalidation']:
    PRIOR_PRODUCT_FINGERPRINTS[m]=provenance.get('product_fingerprint') or product_fingerprint(record(m,'verified-existing-products')['products'])
   if m in OVERLAY['force_package_revalidation'] and not provenance.get('package_options_validated',False):
    missing.append({'module':m,'reason':'old direct-compiler product requires actual package options','action':'necessary-package-option-revalidation'});continue
   reused[m]={'module':m,'source_sha256':e['source_sha256'],'directImports':di,**provenance}
  except Exception as err:missing.append({'module':m,'reason':str(err),'action':'compile-minimal-required-prerequisite'})
 for m in external:require(any((Path(p)/(m.replace('.','/')+'.olean')).is_file() for p in roots),'Missing non-Stacks prerequisite: '+m)
 # Recheck sealed native dependencies before removing old47 outputs. Mathlib
 # has now been acquired and checked in LEAN_PATH above; it is not a Colib root.
 for m,e in restored.items():
  if e['provenance']=='local-repair-package-accepted':
   require(set(e['dependency_product_fingerprints'])==set(NODES[m]['source_imports'])&NODES.keys(),'Missing local native dependency gate')
   for d,expected in e['dependency_product_fingerprints'].items():require(product_fingerprint(record(d,'local-input-identity-check')['products'])==expected,'Local repair dependency product identity changed: '+d)
 remaining=set(NODES)-reused.keys()
 # Remove generated stale outputs only for modules this run must compile.
 # Cached dependents cannot become ready until these predecessors finish.
 for m in remaining:
  for p in products(m):
   if p.is_file():p.unlink()
 write('preflight.json',{'pins':PINS,'compiler':version,'branch_parent':PLAN['branch_parent'],'lower_source_revision':PLAN['lower_source_revision'],'plan_sha256':EFFECTIVE_PLAN_SHA256,'base_plan_sha256':OVERLAY['base_plan_sha256'],'candidate_count':len(CANDIDATES),'reused_count':len(reused),'reused_local_candidate_count':len(CANDIDATES&reused.keys()),'compile_candidates':sorted(CANDIDATES&remaining),'necessary_prerequisite_revalidation':missing,'new_compile_count':len(remaining),'no_kernel_replay':True,'accepted_local_options':PLAN['accepted_local_options']})
 print(f'PREFLIGHT {len(CANDIDATES)} frozen candidates; {len(CANDIDATES&reused.keys())} exact local candidates reused; {len(remaining)} necessary direct compiles; {len(reused)} imported products reused.',flush=True)
 return env,version,reused

def compile_one(m,env):
 paths=products(m);paths[0].parent.mkdir(parents=True,exist_ok=True)
 log=OUT/'logs'/(m+'.log');log.parent.mkdir(parents=True,exist_ok=True)
 command=['lean','-j1',*options(m),'-o',str(paths[0]),'-i',str(paths[3]),str(source(m))]
 started=time.time()
 execution={'module':m,'source_sha256':NODES[m]['source_sha256'],'command':command,'package_options':options(m),'compiler_exit':None,'status':'started'}
 write(m+'.execution.json',execution)
 with log.open('w') as out:p=subprocess.run(command,cwd=ROOT/'.lake/packages/Stacks' if owner(m)=='Stacks' else ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
 execution.update(compiler_exit=p.returncode,status='compiler-finished',seconds=time.time()-started)
 execution['diagnostics']={'warning_lines':sum(': warning' in line for line in log.read_text().splitlines()),'error_lines':sum(': error' in line for line in log.read_text().splitlines())};write(m+'.execution.json',execution)
 require(p.returncode==0,f'Compiler exit {p.returncode}: {m}\n'+log.read_text()[-12000:])
 require(sha(source(m))==NODES[m]['source_sha256'],'Source changed while compiling')
 r=record(m,'compiled-this-proof-run-with-package-options',p.returncode);r.update(seconds=time.time()-started,command=command,package_options=options(m),package_options_validated=True,diagnostics=execution['diagnostics'],source_dag_sha256=CURRENT_SOURCE_FINGERPRINTS[m],dependency_product_fingerprints={d:dependency_product_identity(d) for d in NODES[m]['source_imports'] if d in NODES});return r

def main():
 start=time.time();results={};reused={};failed={};blocked={};complete=set();invalidated={};code=1;version=None
 try:
  env,version,reused=initialize();remaining=set(NODES)
  reverse={m:set() for m in NODES}
  for m,e in NODES.items():
   for d in e['source_imports']:
    if d in reverse:reverse[d].add(m)
  def changed_products(m,r):
   previous=PRIOR_PRODUCT_FINGERPRINTS.get(m)
   if previous is None or previous==product_fingerprint(r['products']):return
   seen=set();todo=[m]
   while todo:
    for d in reverse[todo.pop()]:
     if d not in seen:seen.add(d);todo.append(d)
   for d in sorted(seen&reused.keys()):
    require(d not in complete and d in remaining,'Changed dependency reached an already accepted cached descendant: '+d)
    DEPENDENCY_PRODUCT_IDENTITIES.pop(d,None)
    invalidated[d]={'changed_predecessor':m,'reason':'dependency product bytes changed after necessary package revalidation','original_provenance':reused.pop(d)['provenance']}
    # Every invalidated descendant remains in the same DAG queue; never load its old bytes.
    for p in products(d):
     if p.is_file():p.unlink()
   write('necessary-cache-revalidation.json',invalidated)
  with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
   active={}
   while remaining or active:
    # Cached bytes are available, not necessarily dependency-ready. Settle both
    # failure propagation and cached readiness through the full frozen DAG.
    # Unrelated ready work continues; no cached product is recompiled here.
    while True:
     bad={m:sorted(set(NODES[m]['source_imports'])&(failed.keys()|blocked.keys())) for m in remaining};bad={m:v for m,v in bad.items() if v}
     for m,why in bad.items():remaining.remove(m);blocked[m]=why
     ready_cached={m for m in remaining if m in reused and (set(NODES[m]['source_imports'])&NODES.keys())<=complete}
     remaining.difference_update(ready_cached);complete.update(ready_cached)
     if not bad and not ready_cached:break
    ready=sorted((m for m in remaining if (set(NODES[m]['source_imports'])&NODES.keys())<=complete),key=lambda m:(m not in CANDIDATES,m))
    for m in ready[:8-len(active)]:remaining.remove(m);active[pool.submit(compile_one,m,env)]=m
    if not active:
     require(not remaining,'DAG stalled without known failure: '+str(sorted(remaining)[:10]));break
    done,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
    for future in done:
     m=active.pop(future)
     try:
      r=future.result();changed_products(m,r);results[m]=r;complete.add(m);print(f'PASS {len(results)} {m}',flush=True)
     except Exception as error:failed[m]=str(error);print('FAIL '+str(error),flush=True)
    write('progress.json',{'compiled':sorted(results),'failures':failed,'blocked':blocked,'active':sorted(active.values()),'pending':sorted(remaining)})
  code=0 if CANDIDATES<=complete and not failed and not blocked else 1
 except Exception as error:failed['__preflight_or_driver__']=str(error);print('FAIL '+str(error),flush=True)
 # Export only newly compiled products and relevant reused local candidate inputs.
 exported=list(results.values())
 for m,e in reused.items():
  if m in CANDIDATES and m not in results:
   r=record(m,e['provenance']);r.update(package_options_validated=e.get('package_options_validated',False),original_run_id=e.get('original_run_id'),original_compiler_exit=e.get('original_compiler_exit'),original_package_options=e.get('original_package_options'),current_source_dag_dependencies_ready=m in complete,exact_baseline_reuse=m in OVERLAY['reuse_baseline_roots']);exported.append(r)
 producer={'schema':1,'repository':os.environ.get('GITHUB_REPOSITORY'),'head':os.environ.get('GITHUB_SHA'),'run_id':os.environ.get('GITHUB_RUN_ID'),'run_attempt':os.environ.get('GITHUB_RUN_ATTEMPT'),'branch_parent':PLAN['branch_parent'],'lower_source_revision':PLAN['lower_source_revision'],'pins':PINS,'compiler':version,'plan_sha256':EFFECTIVE_PLAN_SHA256,'base_plan_sha256':OVERLAY['base_plan_sha256'],'build_true_exit':code,'status':'complete-frozen-candidate-compiler-check' if code==0 else 'partial-or-failed','candidate_count':len(CANDIDATES),'completed_candidate_count':len(CANDIDATES&complete),'newly_compiled_count':len(results),'reused_candidate_count':len(CANDIDATES&reused.keys()),'reused_import_count':len(reused),'reused_dependency_ready_count':len(reused.keys()&complete),'reused_candidate_dependency_ready_count':len(CANDIDATES&reused.keys()&complete),'failures':failed,'blocked_dependents':blocked,'modules':exported,'seconds':time.time()-start,'no_kernel_replay':True,'whole_strict_a1_complete':False,'package_acceptance_caveat':'Old47 require new package acceptance; exact db74 baseline reuse is separately counted. No full strict A1 or kernel replay claim.','source_manifest_count':len(PLAN['manifests'])+len(OVERLAY['manifests']),'phase':2,'reused_baseline_candidate_count':len(CANDIDATES&complete&set(OVERLAY['reuse_baseline_roots'])),'package_accepted_candidate_count':len(CANDIDATES&(results.keys()|{m for m,e in reused.items() if e.get('package_options_validated',False) and m in complete})),'necessary_cache_revalidation':invalidated,'no_new_mathematical_roots':True}
 write('producer.json',producer);write('reused-input-identities.json',reused)
 name='strict-a1-frozen-proofs.tar'
 with tarfile.open(OUT/name,'w') as tar:
  tar.add(OUT/'producer.json',arcname='producer.json')
  for e in exported:
   for p in e['products']:
    path=ROOT/p['path'];require(path.is_file() and not path.is_symlink(),'Unsafe exported product');tar.add(path,arcname=p['path'],recursive=False)
 (OUT/(name+'.sha256')).write_text(sha(OUT/name)+'  '+name+'\n')
 print(f'FINAL build_true_exit={code} candidate_complete={producer["completed_candidate_count"]}/{len(CANDIDATES)} compiled={len(results)} failed={len(failed)} blocked={len(blocked)}',flush=True);return code
if __name__=='__main__':sys.exit(main())
