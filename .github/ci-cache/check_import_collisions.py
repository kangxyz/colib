#!/usr/bin/env python3
"""Diagnose every candidate import collision without changing the main build result."""
import argparse,json,os,pathlib,signal,subprocess,tempfile,time


def check_groups(groups, root, output, command, timeout):
    root=pathlib.Path(root).resolve(); output=pathlib.Path(output).resolve()
    output.mkdir(parents=True,exist_ok=True)
    results=[]
    with tempfile.TemporaryDirectory(prefix='import-collision-', dir=output) as directory:
        for index,group in enumerate(groups,1):
            modules=list(dict.fromkeys(group['modules']))
            if len(modules)<2:
                raise ValueError(f'group {index} needs at least two distinct modules')
            if any(not all(part.isidentifier() for part in module.split('.')) for module in modules):
                raise ValueError(f'group {index} has invalid module name')
            source=pathlib.Path(directory)/f'Group{index}.lean'
            source.write_text('module\n'+''.join(f'public import {module}\n' for module in modules))
            log=output/f'group-{index}.log'; start=time.monotonic()
            with log.open('w') as stream:
                process=subprocess.Popen(command+[str(source)],cwd=root,stdout=stream,
                    stderr=subprocess.STDOUT,start_new_session=True)
                try:
                    code=process.wait(timeout=timeout)
                    status='passed' if code==0 else 'failed'
                except subprocess.TimeoutExpired:
                    try: os.killpg(process.pid,signal.SIGTERM)
                    except ProcessLookupError: pass
                    try: process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        try: os.killpg(process.pid,signal.SIGKILL)
                        except ProcessLookupError: pass
                        process.wait()
                    status='timeout'; code=None
            receipt={'group':group.get('group',index),'modules':modules,'status':status,
                     'exit_code':code,'seconds':round(time.monotonic()-start,2),'log':str(log)}
            results.append(receipt);print(json.dumps(receipt),flush=True)
            if status!='passed': print(log.read_text(),flush=True)
            (output/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    return int(any(item['status']!='passed' for item in results))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--groups',required=True)
    parser.add_argument('--root',default='.')
    parser.add_argument('--output',required=True)
    parser.add_argument('--timeout',type=int,default=120)
    parser.add_argument('--direct-lean',action='store_true')
    args=parser.parse_args()
    groups=json.loads(pathlib.Path(args.groups).read_text())
    if not groups: raise SystemExit('No candidate groups supplied; diagnostic not run')
    command=([] if args.direct_lean else ['lake','env'])+['lean','-j1','-M12000']
    raise SystemExit(check_groups(groups,args.root,args.output,command,args.timeout))
