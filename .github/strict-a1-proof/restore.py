#!/usr/bin/env python3
"""Restore only verified native inputs; never use Lake to schedule a build."""
from common import *
import argparse,importlib.util,shutil,tarfile,tempfile,zipfile
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
with zipfile.ZipFile(z) as zip:
 require(zip.namelist()==['strict-a1-dependencies.tar'],'Unexpected dependency ZIP members')
 with zip.open('strict-a1-dependencies.tar') as inp,(WORK/'dependencies.tar').open('wb') as out:shutil.copyfileobj(inp,out)
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
base=json.loads(gzip.decompress((HERE/'lower-cache.json.gz').read_bytes()))
a=WORK/'colib-native.tar';download('repos/kangxyz/colib/releases/assets/734189404',a,77998080,'d40bd0042ed505d5b92d8dd30b9e9af61837d7bea4820f5166a720963a648cb9')
prefix=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip());leantar=prefix/'bin/leantar'
require(sha(leantar)=='06d613dffd2a6fd996b095bfd835c2bb720886f9eb7e13ed2adddd7df4507bf3','Wrong pinned leantar identity')
with tarfile.open(a) as tar:
 members={m.name.removeprefix('./'):m for m in safe_members(tar)}
 prod=json.load(tar.extractfile(members['producer.json']));require(prod['revision']==PLAN['lower_source_revision'] and PINS['lean_commit'] in prod['compiler'],'Wrong lower producer')
 for e in base:
  m=e['module'];require(sha(source(m))==NODES[m]['source_sha256'],'Changed db74 lower source')
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
write('restored.json',restored)
print('Restored all applicable exact inputs; full source/hash/import preflight follows.',flush=True)
