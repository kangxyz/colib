#!/usr/bin/env python3
"""Restore only verified native inputs; never use Lake to schedule a build."""
from common import *
import argparse,importlib.util,shutil,tarfile,tempfile,zipfile,base64
WORK=OUT/'restore';WORK.mkdir(parents=True,exist_ok=True)
def download(api,path,size,digest):
 if not(path.is_file() and path.stat().st_size==size and sha(path)==digest):
  accept='application/json' if '/actions/artifacts/' in api else 'application/octet-stream'
  with path.open('wb') as out:subprocess.run(['gh','api',api,'-H','Accept: '+accept],stdout=out,check=True)
 require(path.stat().st_size==size and sha(path)==digest,'Downloaded size/SHA mismatch: '+api)
# Exact official pinned Stacks cache, using the repository's verified checkpoint loader.
spec=importlib.util.spec_from_file_location('checkpoint',ROOT/'.github/ci-cache/checkpoint.py');cp=importlib.util.module_from_spec(spec);spec.loader.exec_module(cp)
a=ROOT/'.lake/ci-checkpoints/stacks.tar.zst';a.parent.mkdir(parents=True,exist_ok=True)
download('repos/kangxyz/colib/releases/assets/733969670',a,1586654451,'23436ff5612fb91f32ce13916df8076e8bc3af302d2024ab4600801d87aa817d')
cp.supported(ROOT,materialized=True);cp.restore(argparse.Namespace(root=ROOT,layer='stacks',native_cache=Path(os.environ['LAKE_CACHE_DIR']).absolute(),metadata=None,github_output=None,input=a))
print('Restored exact official pinned Stacks checkpoint.',flush=True)
# Exact successful 445 dependency products from the already finished independent run.
z=WORK/'dependencies.zip';download('repos/kangxyz/colib/actions/artifacts/13846402806/zip',z,68251580,'8d80fe8ca19a9a3eab54e64735ac6d0d6e82c4786313ea3b2f8de59deee04552')
with zipfile.ZipFile(z) as archive_zip:
 require(archive_zip.namelist()==['strict-a1-dependencies.tar'],'Unexpected dependency ZIP members')
 with archive_zip.open('strict-a1-dependencies.tar') as inp,(WORK/'dependencies.tar').open('wb') as out:shutil.copyfileobj(inp,out)
t=WORK/'dependencies.tar';require(sha(t)=='36a1308da79a65161af9c8dad665a528cae5278fde4970843e6c14d3fde8e5fb','Dependency inner archive mismatch')
restored={}
with tarfile.open(t) as tar:
 members={m.name:m for m in safe_members(tar)};p=json.load(tar.extractfile(members['producer.json']))
 require(p['head']=='b5e56f7c6de88b6d48dd1fbaa71b311be6018251' and p['run_id']=='43000467920' and p['build_true_exit']==0 and p['completed_count']==445 and p['pins']==PINS,'Wrong dependency producer')
 for e in p['modules']:
  m=e['module']
  if m not in NODES:continue
  require(sha(source(m))==e['source_sha256'],'Dependency source changed: '+m)
  for entry in e['products']:
   dest=ROOT/entry['path'];require(dest in products(m),'Wrong dependency destination')
   blob=tar.extractfile(members[entry['path']]).read();require(len(blob)==entry['size'] and hashlib.sha256(blob).hexdigest()==entry['sha256'],'Dependency product mismatch')
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
  bundle(m);restored[m]={'provenance':'ci-run-43000467920','source_sha256':e['source_sha256']}
print('Restored exact already-compiled remote dependency products: '+str(len(restored)),flush=True)
# Exact db74 native package LTARs, with independently mapped ilean identities.
base=json.loads(gzip.decompress((HERE/'lower-cache.json.gz').read_bytes()))+OVERLAY['lower_cache_additions']
base_graph={m:dict(e) for m,e in ORIGINAL_NODES.items()}
for e in OVERLAY['lower_cache_additions']:base_graph[e['module']]=NODES[e['module']]
base_fingerprints=source_dag_fingerprints(base_graph);current_fingerprints=source_dag_fingerprints(NODES)
a=WORK/'colib-native.tar';download('repos/kangxyz/colib/releases/assets/734189404',a,77998080,'d40bd0042ed505d5b92d8dd30b9e9af61837d7bea4820f5166a720963a648cb9')
prefix=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip());leantar=prefix/'bin/leantar'
require(sha(leantar)=='06d613dffd2a6fd996b095bfd835c2bb720886f9eb7e13ed2adddd7df4507bf3','Wrong pinned leantar identity')
with tarfile.open(a) as tar:
 members={m.name.removeprefix('./'):m for m in safe_members(tar)}
 prod=json.load(tar.extractfile(members['producer.json']));require(prod['revision']==PLAN['lower_source_revision'] and PINS['lean_commit'] in prod['compiler'],'Wrong lower producer')
 for e in base:
  m=e['module'];require(sha(source(m))==e.get('source_sha256',ORIGINAL_NODES[m]['source_sha256']),'Changed db74 lower source')
  require(base_fingerprints[m]==current_fingerprints[m],'Changed db74 dependency-source identity: '+m)
  blob=tar.extractfile(members[e['ltar']]).read();require(hashlib.sha256(blob).hexdigest()==e['ltar_sha256'],'Wrong lower LTAR')
  with tempfile.TemporaryDirectory(dir=WORK) as tmp:
   tmp=Path(tmp);ltar=tmp/e['ltar'];ltar.write_bytes(blob);lib=tmp/'lib';ir=tmp/'ir';lib.mkdir();ir.mkdir()
   subprocess.run([str(leantar),'--jobs','1','-x','-j','-'],input=json.dumps([{'file':str(ltar),'base':[str(lib),str(ir)],'hash':e['depHash']}]),text=True,check=True)
   for item in e['products']:
    p=tmp/item['path'];require(p.is_file() and not p.is_symlink() and p.stat().st_size==item['size'] and sha(p)==item['sha256'],'Wrong lower decoded product')
   info=json.loads(next(lib.glob('*.ilean')).read_text());require(info['module']==m and [v[0] for v in info['directImports']]==NODES[m]['source_imports'],'Lower source/ilean identity mismatch')
   for suffix,dest in zip(SUFFIXES,products(m)):
    src=lib/(m.split('.')[-1]+suffix);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
  bundle(m);restored[m]={'provenance':'official-native-db74-asset-734189404','source_sha256':NODES[m]['source_sha256']}
print('Restored exact db74 lower modules: '+str(len(base)),flush=True)
# Only relevant local accepted products, never claim package-options validation.
c=json.loads((HERE/'local-cutoff.json').read_text());require(sha(HERE/'local-cutoff.json')==PLAN['local_cutoff_sha256'],'Wrong local cutoff')
a=HERE/'local-accepted-49-and-4.tar.gz';require(a.stat().st_size==PLAN['local_archive_bytes'] and sha(a)==PLAN['local_archive_sha256'],'Wrong local archive')
with tarfile.open(a) as tar:
 members={m.name:m for m in safe_members(tar)}
 for e in c['entries']:
  m=e['module']
  if m not in NODES or e['source_sha256']!=NODES[m]['source_sha256']:continue
  require(sha(source(m))==e['source_sha256'],'Local source mismatch')
  for item in e['products']:
   name=item['archive_path'];suffix=next(s for s in sorted(SUFFIXES,key=len,reverse=True) if name.endswith(s));dest=Path(str(productroot(m)/m.replace('.','/'))+suffix)
   blob=tar.extractfile(members[name]).read();require(len(blob)==item['size'] and hashlib.sha256(blob).hexdigest()==item['sha256'],'Local product mismatch')
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
  bundle(m);restored[m]={'provenance':'local-accepted-direct-compiler-only','source_sha256':e['source_sha256'],'original_run_id':e['run_id'],'package_options_validated':False}
# Restore successful partial outputs without upgrading old import-only products.
z=WORK/'prior-proof.zip';download('repos/kangxyz/colib/actions/artifacts/13852113966/zip',z,125903188,'f103398973ebb56ac3bdfaefcc3bf8bddc5eec43514efdc6d72a5ce614a7828e')
with zipfile.ZipFile(z) as archive_zip:
 require(archive_zip.namelist()==['strict-a1-frozen-proofs.tar'],'Unexpected prior proof ZIP members')
 with archive_zip.open('strict-a1-frozen-proofs.tar') as inp,(WORK/'prior-proof.tar').open('wb') as out:shutil.copyfileobj(inp,out)
t=WORK/'prior-proof.tar';require(sha(t)=='594dd9baa2411359e645324c819b57159b22e4ad702f01a5fea4e6b8210073b4','Prior proof tar SHA mismatch')
old_fingerprints=source_dag_fingerprints(ORIGINAL_NODES)
with tarfile.open(t) as tar:
 members={m.name:m for m in safe_members(tar)};prior_blob=tar.extractfile(members['producer.json']).read()
 require(hashlib.sha256(prior_blob).hexdigest()=='550db8548161e806c01a922fb985acd6deaf48d68d5a39c93f61ec0cc72defbd','Prior producer identity mismatch')
 prior=json.loads(prior_blob);require(prior['head']==OVERLAY['previous_head'] and prior['run_id']==OVERLAY['previous_run_id'] and prior['pins']==PINS and prior['build_true_exit']==1,'Wrong partial producer')
 accepted=set();new_seen=set();old_seen=set()
 for e in prior['modules']:
  m=e['module'];is_new=e['provenance']=='compiled-this-proof-run-with-package-options'
  require(is_new or e['provenance']=='local-accepted-direct-compiler-only','Unknown prior provenance')
  (new_seen if is_new else old_seen).add(m)
  require({entry['path'] for entry in e['products']}=={p.relative_to(ROOT).as_posix() for p in products(m)},'Wrong prior product set')
  blobs={}
  for entry in e['products']:
   blob=tar.extractfile(members[entry['path']]).read();require(len(blob)==entry['size'] and hashlib.sha256(blob).hexdigest()==entry['sha256'],'Prior product size/SHA mismatch');blobs[entry['path']]=blob
  if m not in NODES or e['source_sha256']!=NODES[m]['source_sha256'] or old_fingerprints[m]!=current_fingerprints[m]:continue
  require(sha(source(m))==e['source_sha256'],'Prior current source mismatch')
  if is_new:
   require(m in OVERLAY['prior_partial_eligible_modules'] and e['compiler_exit']==0,'Ineligible partial module')
   require(e['package_options']==[v for v in e['command'] if v.startswith('-D')] and registered_options_equivalent(e['package_options'],package_options(m)),'Prior package options mismatch')
  else:require(e['package_options_validated'] is False and e['compiler_exit'] is None,'Old import-only acceptance was upgraded')
  for path,blob in blobs.items():
   dest=ROOT/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
  bundle(m);restored[m]={'provenance':'prior-proof-package-accepted' if is_new else 'local-accepted-direct-compiler-only','source_sha256':e['source_sha256'],'source_dag_sha256':current_fingerprints[m],'original_run_id':prior['run_id'] if is_new else e['original_run_id'],'original_head':prior['head'] if is_new else None,'package_options_validated':is_new,'original_package_options':e.get('package_options'),'original_compiler_exit':e['compiler_exit'],'product_fingerprint':product_fingerprint(e['products']),'products':e['products']}
  if is_new:accepted.add(m)
 require(len(new_seen)==633 and len(old_seen)==47 and accepted==set(OVERLAY['prior_partial_eligible_modules']),'Prior reuse scope differs from frozen plan')
print('Restored eligible prior successful package products: '+str(len(accepted))+'; old import-only remains unqualified.',flush=True)
# Four source-frozen local repairs, if present, require their exact successful
# package-option receipts; no post-cutoff mathematical roots are admitted.
local=OVERLAY['local_package_cutoff']
require(local is not None,'Phase2 local cutoff has not been frozen')
manifest=HERE/local['manifest_path'];archive=WORK/local['archive_path']
archive.write_bytes(base64.b64decode((HERE/local['encoded_archive_path']).read_text().strip(),validate=True))
require(sha(manifest)==local['manifest_sha256'] and archive.stat().st_size==local['archive_bytes'] and sha(archive)==local['archive_sha256'],'Wrong local package cutoff')
packet=json.loads(manifest.read_text());require(packet['pins']==PINS,'Local package cutoff pins mismatch')
with tarfile.open(archive) as tar:
 members={m.name:m for m in safe_members(tar)}
 for e in packet['modules']:
  m=e['module'];require(m in NODES and m in local['modules'] and e['compiler_exit']==0,'Wrong local repair scope or exit')
  require(e['source_sha256']==NODES[m]['source_sha256'] and sha(source(m))==e['source_sha256'],'Wrong local repair source')
  require(e['package_options']==package_options(m),'Local repair package options differ')
  # A changed source-DAG makes a historically valid product ineligible,
  # not an archive corruption. It must be recompiled in this same DAG.
  eligible=e['source_dag_sha256']==current_fingerprints[m]
  require(eligible==(m in OVERLAY['local_package_eligible_modules']),'Local source-DAG eligibility differs from frozen plan')
  require(set(e['dependency_product_fingerprints'])==set(NODES[m]['source_imports'])&NODES.keys(),'Missing local repair native dependency identity')
  if eligible:
   for d,expected in e['dependency_product_fingerprints'].items():require(product_fingerprint(record(d,'local-input-identity-check')['products'])==expected,'Local repair dependency product identity changed: '+d)
  require({entry['path'] for entry in e['products']}=={p.relative_to(ROOT).as_posix() for p in products(m)},'Wrong local repair product set')
  for entry in e['products']:
   blob=tar.extractfile(members[entry['archive_path']]).read();require(len(blob)==entry['size'] and hashlib.sha256(blob).hexdigest()==entry['sha256'],'Local repair product mismatch')
   if eligible:
    dest=ROOT/entry['path'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
  if not eligible:continue
  bundle(m);restored[m]={'provenance':'local-repair-package-accepted','source_sha256':e['source_sha256'],'source_dag_sha256':current_fingerprints[m],'original_run_id':e['run_id'],'package_options_validated':True,'original_package_options':e['package_options'],'original_compiler_exit':0,'dependency_product_fingerprints':e['dependency_product_fingerprints'],'product_fingerprint':product_fingerprint(e['products']),'products':e['products']}
require(set(e['module'] for e in packet['modules'])==set(local['modules']),'Local cutoff module mismatch')
# Exact newly successful phase2 products. Reused phase2 bundles are integrity
# checked but not reclassified or used to override their original provenance.
z=WORK/'phase2-proof.zip';download('repos/kangxyz/colib/actions/artifacts/13856407932/zip',z,7341425,'f22fee66a7463acee7338a3d0e254c7b22409e8017b1d659cfa59a45b0f41635')
with zipfile.ZipFile(z) as archive_zip:
 require(archive_zip.namelist()==['strict-a1-frozen-proofs.tar'],'Unexpected phase2 proof ZIP members')
 with archive_zip.open('strict-a1-frozen-proofs.tar') as inp,(WORK/'phase2-proof.tar').open('wb') as out:shutil.copyfileobj(inp,out)
t=WORK/'phase2-proof.tar';require(sha(t)=='c1d008dfa7eae5545372997524baf8b821d4142fd03f64b2493edc217ddfacde','Phase2 proof tar SHA mismatch')
with tarfile.open(t) as tar:
 members={m.name:m for m in safe_members(tar)};producer_blob=tar.extractfile(members['producer.json']).read()
 require(hashlib.sha256(producer_blob).hexdigest()=='0f2d1d8040a03ce23409dc0276ee18065b95af82302d4492da9a53868d598e6e','Phase2 producer identity mismatch')
 phase2=json.loads(producer_blob)
 require(phase2['head']=='ef008c3d3795c9e8a4efa42aeb22de0e478376ad' and phase2['run_id']=='43023778647' and phase2['pins']==PINS and phase2['build_true_exit']==1 and phase2['phase']==2,'Wrong phase2 producer')
 seen=set();accepted=set()
 for e in phase2['modules']:
  m=e['module'];require(m not in seen,'Duplicate phase2 module');seen.add(m)
  require({entry['path'] for entry in e['products']}=={p.relative_to(ROOT).as_posix() for p in products(m)},'Wrong phase2 product set')
  blobs={}
  for entry in e['products']:
   blob=tar.extractfile(members[entry['path']]).read();require(len(blob)==entry['size'] and hashlib.sha256(blob).hexdigest()==entry['sha256'],'Phase2 product size/SHA mismatch');blobs[entry['path']]=blob
  if e['provenance']!='compiled-this-proof-run-with-package-options':continue
  require(m in NODES and e['source_sha256']==NODES[m]['source_sha256'] and sha(source(m))==e['source_sha256'],'Phase2 source mismatch')
  require(e['source_dag_sha256']==current_fingerprints[m],'Phase2 dependency source identity changed')
  require(e['compiler_exit']==0 and e['package_options_validated'] is True and e['package_options']==package_options(m) and e['package_options']==[v for v in e['command'] if v.startswith('-D')],'Phase2 package options mismatch')
  require(set(e['dependency_product_fingerprints'])==set(NODES[m]['source_imports'])&NODES.keys(),'Missing phase2 native input identities')
  for path,blob in blobs.items():
   dest=ROOT/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
  bundle(m);restored[m]={'provenance':'phase2-proof-package-accepted','source_sha256':e['source_sha256'],'source_dag_sha256':current_fingerprints[m],'original_run_id':phase2['run_id'],'original_head':phase2['head'],'package_options_validated':True,'original_package_options':e['package_options'],'original_compiler_exit':0,'dependency_product_fingerprints':e['dependency_product_fingerprints'],'product_fingerprint':product_fingerprint(e['products']),'products':e['products']};accepted.add(m)
 require(len(seen)==120 and accepted==set(OVERLAY['phase2_partial_eligible_modules']),'Phase2 reuse scope differs from frozen plan')
print('Restored exact phase2 new successful bundles: '+str(len(accepted)),flush=True)
# Exact newly successful phase3 products. Reused phase3 bundles are integrity
# checked but not reclassified or used to override their original provenance.
z=WORK/'phase3-proof.zip';download('repos/kangxyz/colib/actions/artifacts/13861032162/zip',z,10177296,'95fd6bcc61ae39297ed92e714a3d909722c570cef47dbe52ab0ed7d570c646ff')
with zipfile.ZipFile(z) as archive_zip:
 require(archive_zip.namelist()==['strict-a1-frozen-proofs.tar'],'Unexpected phase3 proof ZIP members')
 with archive_zip.open('strict-a1-frozen-proofs.tar') as inp,(WORK/'phase3-proof.tar').open('wb') as out:shutil.copyfileobj(inp,out)
t=WORK/'phase3-proof.tar';require(sha(t)=='0f69835d631858bc309dffec8fd64305edf79386a0508e31d0076cf983e39b6f','Phase3 proof tar SHA mismatch')
with tarfile.open(t) as tar:
 members={m.name:m for m in safe_members(tar)};producer_blob=tar.extractfile(members['producer.json']).read()
 require(hashlib.sha256(producer_blob).hexdigest()=='27c81539737c1f18279d41629f16ba760527ef5f57a95104852d3501c3bc28db','Phase3 producer identity mismatch')
 phase3=json.loads(producer_blob)
 require(phase3['head']=='0bb9624894eadc3f808e3c59c9ae7100e6114577' and phase3['run_id']=='43029251170' and phase3['pins']==PINS and phase3['build_true_exit']==1 and phase3['phase']==3,'Wrong phase3 producer')
 seen=set();accepted=set()
 for e in phase3['modules']:
  m=e['module'];require(m not in seen,'Duplicate phase3 module');seen.add(m)
  require({entry['path'] for entry in e['products']}=={p.relative_to(ROOT).as_posix() for p in products(m)},'Wrong phase3 product set')
  blobs={}
  for entry in e['products']:
   blob=tar.extractfile(members[entry['path']]).read();require(len(blob)==entry['size'] and hashlib.sha256(blob).hexdigest()==entry['sha256'],'Phase3 product size/SHA mismatch');blobs[entry['path']]=blob
  if e['provenance']!='compiled-this-proof-run-with-package-options':continue
  require(m in NODES and e['source_sha256']==NODES[m]['source_sha256'] and sha(source(m))==e['source_sha256'],'Phase3 source mismatch')
  require(e['source_dag_sha256']==current_fingerprints[m],'Phase3 dependency source identity changed')
  require(e['compiler_exit']==0 and e['package_options_validated'] is True and e['package_options']==package_options(m) and e['package_options']==[v for v in e['command'] if v.startswith('-D')],'Phase3 package options mismatch')
  require(set(e['dependency_product_fingerprints'])==set(NODES[m]['source_imports'])&NODES.keys(),'Missing phase3 native input identities')
  for path,blob in blobs.items():
   dest=ROOT/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
  bundle(m);restored[m]={'provenance':'phase3-proof-package-accepted','source_sha256':e['source_sha256'],'source_dag_sha256':current_fingerprints[m],'original_run_id':phase3['run_id'],'original_head':phase3['head'],'package_options_validated':True,'original_package_options':e['package_options'],'original_compiler_exit':0,'dependency_product_fingerprints':e['dependency_product_fingerprints'],'product_fingerprint':product_fingerprint(e['products']),'products':e['products']};accepted.add(m)
 require(len(seen)==149 and accepted==set(OVERLAY['phase3_partial_eligible_modules']),'Phase3 reuse scope differs from frozen plan')
print('Restored exact phase3 new successful bundles: '+str(len(accepted)),flush=True)
# Exact newly successful phase4 products. Reused phase4 bundles are integrity
# checked but not reclassified or used to override their original provenance.
z=WORK/'phase4-proof.zip';download('repos/kangxyz/colib/actions/artifacts/13860554914/zip',z,10347321,'3824866425551e7cc99063903938befcf1e6d26474248a0f06b621c91c5850be')
with zipfile.ZipFile(z) as archive_zip:
 require(archive_zip.namelist()==['strict-a1-frozen-proofs.tar'],'Unexpected phase4 proof ZIP members')
 with archive_zip.open('strict-a1-frozen-proofs.tar') as inp,(WORK/'phase4-proof.tar').open('wb') as out:shutil.copyfileobj(inp,out)
t=WORK/'phase4-proof.tar';require(sha(t)=='77ea29ca4271adc53af2ef9782d808e3a233dd590c8eba77f0fdf461f755d097','Phase4 proof tar SHA mismatch')
with tarfile.open(t) as tar:
 members={m.name:m for m in safe_members(tar)};producer_blob=tar.extractfile(members['producer.json']).read()
 require(hashlib.sha256(producer_blob).hexdigest()=='1f3d1b0f152f81402dbbdc4c64b15a1e5c1c5eaa8dc3142c2d323fdc0d543f5e','Phase4 producer identity mismatch')
 phase4=json.loads(producer_blob)
 require(phase4['head']=='f24a801f7fe1093313e9ff9d60f3245da034efe9' and phase4['run_id']=='43032115738' and phase4['pins']==PINS and phase4['build_true_exit']==1 and phase4['phase']==4,'Wrong phase4 producer')
 seen=set();accepted=set()
 for e in phase4['modules']:
  m=e['module'];require(m not in seen,'Duplicate phase4 module');seen.add(m)
  require({entry['path'] for entry in e['products']}=={p.relative_to(ROOT).as_posix() for p in products(m)},'Wrong phase4 product set')
  blobs={}
  for entry in e['products']:
   blob=tar.extractfile(members[entry['path']]).read();require(len(blob)==entry['size'] and hashlib.sha256(blob).hexdigest()==entry['sha256'],'Phase4 product size/SHA mismatch');blobs[entry['path']]=blob
  if e['provenance']!='compiled-this-proof-run-with-package-options':continue
  require(m in NODES and e['source_sha256']==NODES[m]['source_sha256'] and sha(source(m))==e['source_sha256'],'Phase4 source mismatch')
  require(e['source_dag_sha256']==current_fingerprints[m],'Phase4 dependency source identity changed')
  require(e['compiler_exit']==0 and e['package_options_validated'] is True and e['package_options']==package_options(m) and e['package_options']==[v for v in e['command'] if v.startswith('-D')],'Phase4 package options mismatch')
  require(set(e['dependency_product_fingerprints'])==set(NODES[m]['source_imports'])&NODES.keys(),'Missing phase4 native input identities')
  for path,blob in blobs.items():
   dest=ROOT/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
  bundle(m);restored[m]={'provenance':'phase4-proof-package-accepted','source_sha256':e['source_sha256'],'source_dag_sha256':current_fingerprints[m],'original_run_id':phase4['run_id'],'original_head':phase4['head'],'package_options_validated':True,'original_package_options':e['package_options'],'original_compiler_exit':0,'dependency_product_fingerprints':e['dependency_product_fingerprints'],'product_fingerprint':product_fingerprint(e['products']),'products':e['products']};accepted.add(m)
 require(len(seen)==151 and accepted==set(OVERLAY['phase4_partial_eligible_modules']),'Phase4 reuse scope differs from frozen plan')
print('Restored exact phase4 new successful bundles: '+str(len(accepted)),flush=True)
# Exact newly successful phase5 products. Reused phase5 bundles are integrity
# checked but not reclassified or used to override their original provenance.
z=WORK/'phase5-proof.zip';download('repos/kangxyz/colib/actions/artifacts/13861304886/zip',z,10478598,'6b3f29663c04b1390e05ac0dcd57c865164022b19429d4b60e124b790f7944ed')
with zipfile.ZipFile(z) as archive_zip:
 require(archive_zip.namelist()==['strict-a1-frozen-proofs.tar'],'Unexpected phase5 proof ZIP members')
 with archive_zip.open('strict-a1-frozen-proofs.tar') as inp,(WORK/'phase5-proof.tar').open('wb') as out:shutil.copyfileobj(inp,out)
t=WORK/'phase5-proof.tar';require(sha(t)=='f73f6f9a3e18a7cb4cdaa153f5654277cb1fb8c5e447b5603fdce09e2b6ece06','Phase5 proof tar SHA mismatch')
with tarfile.open(t) as tar:
 members={m.name:m for m in safe_members(tar)};producer_blob=tar.extractfile(members['producer.json']).read()
 require(hashlib.sha256(producer_blob).hexdigest()=='1a004eb6bd68046149404b3d09ac3d2724506baa935161124faf9e74b3ca7c7b','Phase5 producer identity mismatch')
 phase5=json.loads(producer_blob)
 require(phase5['head']=='8d3d7b13892db4ec694b4d8e39f68fb2aa02c302' and phase5['run_id']=='43034521501' and phase5['pins']==PINS and phase5['build_true_exit']==1 and phase5['phase']==5,'Wrong phase5 producer')
 seen=set();accepted=set()
 for e in phase5['modules']:
  m=e['module'];require(m not in seen,'Duplicate phase5 module');seen.add(m)
  require({entry['path'] for entry in e['products']}=={p.relative_to(ROOT).as_posix() for p in products(m)},'Wrong phase5 product set')
  blobs={}
  for entry in e['products']:
   blob=tar.extractfile(members[entry['path']]).read();require(len(blob)==entry['size'] and hashlib.sha256(blob).hexdigest()==entry['sha256'],'Phase5 product size/SHA mismatch');blobs[entry['path']]=blob
  if e['provenance']!='compiled-this-proof-run-with-package-options':continue
  require(m in NODES and e['source_sha256']==NODES[m]['source_sha256'] and sha(source(m))==e['source_sha256'],'Phase5 source mismatch')
  require(e['source_dag_sha256']==current_fingerprints[m],'Phase5 dependency source identity changed')
  require(e['compiler_exit']==0 and e['package_options_validated'] is True and e['package_options']==package_options(m) and e['package_options']==[v for v in e['command'] if v.startswith('-D')],'Phase5 package options mismatch')
  require(set(e['dependency_product_fingerprints'])==set(NODES[m]['source_imports'])&NODES.keys(),'Missing phase5 native input identities')
  for path,blob in blobs.items():
   dest=ROOT/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
  bundle(m);restored[m]={'provenance':'phase5-proof-package-accepted','source_sha256':e['source_sha256'],'source_dag_sha256':current_fingerprints[m],'original_run_id':phase5['run_id'],'original_head':phase5['head'],'package_options_validated':True,'original_package_options':e['package_options'],'original_compiler_exit':0,'dependency_product_fingerprints':e['dependency_product_fingerprints'],'product_fingerprint':product_fingerprint(e['products']),'products':e['products']};accepted.add(m)
 require(len(seen)==153 and accepted==set(OVERLAY['phase5_partial_eligible_modules']),'Phase5 reuse scope differs from frozen plan')
print('Restored exact phase5 new successful bundles: '+str(len(accepted)),flush=True)
write('restored.json',restored)
print('Restored exact eligible source/dependency identities; remaining old6 require package acceptance.',flush=True)
