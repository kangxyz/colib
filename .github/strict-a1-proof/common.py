import gzip,hashlib,json,os,re,subprocess,tomllib
from pathlib import Path
ROOT=Path.cwd().resolve(); HERE=ROOT/'.github/strict-a1-proof'; OUT=ROOT/'.lake/strict-a1-proof-result'
PLAN=json.loads(gzip.decompress((HERE/'plan.json.gz').read_bytes()))
ORIGINAL_NODES={e['module']:e for e in PLAN['sources']}
OVERLAY=json.loads((HERE/'phase2-overlay.json').read_text())
assert hashlib.sha256((HERE/'plan.json.gz').read_bytes()).hexdigest()==OVERLAY['base_plan_sha256']
assert len(PLAN['candidate_modules'])==OVERLAY['candidate_root_count']==439
assert hashlib.sha256(json.dumps(sorted(PLAN['candidate_modules']),separators=(',',':')).encode()).hexdigest()==OVERLAY['candidate_root_sha256']
assert OVERLAY['no_new_mathematical_roots'] and OVERLAY['no_kernel_replay']
NODES={m:dict(e) for m,e in ORIGINAL_NODES.items()}
for e in OVERLAY['replacement_sources']:NODES[e['module']]=e
assert set(NODES)-set(ORIGINAL_NODES)==set(OVERLAY['additional_dependency_modules'])
PLAN['sources']=list(NODES.values())
EFFECTIVE_PLAN_SHA256=hashlib.sha256((HERE/'plan.json.gz').read_bytes()+b'\0'+(HERE/'phase2-overlay.json').read_bytes()).hexdigest()
SUFFIXES=('.olean','.olean.server','.olean.private','.ilean','.ir','.ir.sig')
PINS={k:PLAN[k] for k in ('lean_version','lean_commit','mathlib_revision','stacks_revision')}
def sha(p):
 with Path(p).open('rb') as s:return hashlib.file_digest(s,'sha256').hexdigest()
def require(c,m):
 if not c:raise RuntimeError(m)
def write(name,obj):
 OUT.mkdir(parents=True,exist_ok=True);p=OUT/name;t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(obj,indent=2)+'\n');t.replace(p)
def owner(m):return 'Stacks' if m.startswith(('Stacks.','StacksCore.','StacksFrontier.')) or m in ('Stacks','StacksCore','StacksFrontier') else 'Colib'
def source(m):return (ROOT/'.lake/packages/Stacks' if owner(m)=='Stacks' else ROOT)/(m.replace('.','/')+'.lean')
def productroot(m):return (ROOT/'.lake/packages/Stacks' if owner(m)=='Stacks' else ROOT)/'.lake/build/lib/lean'
def products(m):return [Path(str(productroot(m)/m.replace('.','/'))+s) for s in SUFFIXES]
def bundle(m):
 paths=products(m)
 for p in paths:require(p.is_file() and not p.is_symlink() and p.stat().st_size>0,'Missing native product: '+str(p))
 info=json.loads(paths[3].read_text());require(info['module']==m,'Wrong ilean identity: '+m)
 actual=[x[0] for x in info['directImports']];expected=NODES[m]['source_imports']
 require(actual==expected or actual==['Init']+expected,'Wrong ilean imports: '+m)
 return paths,info['directImports']
def record(m,provenance,code=None):
 paths,direct=bundle(m)
 return {'module':m,'source_sha256':sha(source(m)),'directImports':direct,'provenance':provenance,'compiler_exit':code,'products':[{'path':p.relative_to(ROOT).as_posix(),'size':p.stat().st_size,'sha256':sha(p)} for p in paths]}
def safe_members(tar):
 seen=set()
 for m in tar:
  p=Path(m.name)
  require(not p.is_absolute() and '..' not in p.parts and '\\' not in m.name,'Unsafe archive path: '+m.name)
  if m.isdir():continue
  name=m.name.removeprefix('./')
  require(name not in seen and m.isfile(),'Unsafe/duplicate archive member: '+m.name)
  seen.add(name);yield m
def imports(path):
    # Lex only the header. Comments or strings inside proof bodies are irrelevant.
    text = path.read_text()
    pos = 0
    def token():
        nonlocal pos
        while pos < len(text):
            if text[pos].isspace():
                pos += 1
            elif text.startswith('--', pos):
                end = text.find('\n', pos)
                pos = len(text) if end < 0 else end + 1
            elif text.startswith('/-', pos):
                pos += 2
                depth = 1
                while depth and pos < len(text):
                    if text.startswith('/-', pos):
                        depth += 1
                        pos += 2
                    elif text.startswith('-/', pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
                require(depth == 0, 'Unclosed header comment: ' + str(path))
            else:
                match = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", text[pos:])
                if match:
                    pos += len(match[0])
                    return match[0]
                return None
        return None
    result = []
    current = token()
    while current in ('module', 'prelude'):
        current = token()
    while current is not None:
        while current in ('public', 'private', 'meta'):
            current = token()
        if current != 'import':
            break
        current = token()
        if current == 'all':
            current = token()
        require(current is not None, 'Missing imported module: ' + str(path))
        result.append(current)
        current = token()
        while current and current[0].isupper() and current not in ('module', 'prelude'):
            result.append(current)
            current = token()
    return result


def package_options(m):
 package=ROOT/'.lake/packages/Stacks' if owner(m)=='Stacks' else ROOT
 config=tomllib.loads((package/'lakefile.toml').read_text())
 opts=dict(config.get('leanOptions',{}))
 for lib in config.get('lean_lib',[]):
  if lib.get('name')==m.split('.')[0]:opts.update(lib.get('leanOptions',{}))
 def flatten(d,prefix=''):
  for k,v in d.items():
   if isinstance(v,dict):yield from flatten(v,prefix+k+'.')
   else:yield prefix+k,v
 return ['-D'+k+'='+(str(v).lower() if isinstance(v,bool) else str(v)) for k,v in flatten(opts)]

def registered_options_equivalent(recorded,current):
 # A successful old compile using the non-weak spelling proves registration.
 # Do not assert this equivalence for failed or unexecuted commands.
 normalize=lambda xs:sorted(x.replace('-Dweak.','-D',1) for x in xs)
 return normalize(recorded)==normalize(current)

def source_dag_fingerprints(nodes):
 memo={};busy=set()
 def calc(m):
  if m in memo:return memo[m]
  require(m not in busy,'Cycle in source identity graph: '+m);busy.add(m)
  if m not in nodes:data=['external',m,{k:PINS[k] for k in ('lean_commit','mathlib_revision','stacks_revision')}]
  else:data=[m,nodes[m]['source_sha256'],[[d,calc(d)] for d in nodes[m]['source_imports']]]
  busy.remove(m);memo[m]=hashlib.sha256(json.dumps(data,separators=(',',':')).encode()).hexdigest();return memo[m]
 for m in nodes:calc(m)
 return memo

def product_fingerprint(entries):
 return hashlib.sha256(json.dumps(sorted((Path(e['path']).name.split('.',1)[-1],e['size'],e['sha256']) for e in entries),separators=(',',':')).encode()).hexdigest()

CURRENT_SOURCE_FINGERPRINTS=source_dag_fingerprints(NODES)
