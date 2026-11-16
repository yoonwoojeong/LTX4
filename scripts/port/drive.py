import os,re,subprocess,sys,time
from concurrent.futures import ThreadPoolExecutor
import threading
SRC='/home/user/src/lean-liquid/src'; MP='/home/user/src/mathport23'; LOG='/home/user/src/portlogs23'
J=int(sys.argv[1]) if len(sys.argv)>1 else 3
def s2p(s):
    r=''.join(x[:1].upper()+x[1:] for x in s.split('_'))
    return ('_' if s.startswith('_') else '')+r+('_' if s.endswith('_') and len(s)>1 else '')
mods={}
for root,_,fs in os.walk(SRC):
    for f in fs:
        if f.endswith('.tlean'):
            m=os.path.relpath(os.path.join(root,f[:-6]),SRC).replace('/','.')
            mods[m]=None
def resolve(i):
    if i in mods: return i
    if i+'.default' in mods: return i+'.default'
    return None
deps={}
for m in mods:
    tok=open(os.path.join(SRC,*m.split('.'))+'.tlean').readline().split()
    assert tok[0]=='IMPORT'
    n=int(tok[1]); pairs=[(tok[2+2*i],int(tok[3+2*i])) for i in range(n)]
    ds=set()
    for name,rel in pairs:
        if rel>=0:
            base=m.split('.')[:-1]
            base=base[:len(base)-rel] if rel else base
            name='.'.join(base+[name])
        d=resolve(name)
        if d and d!=m: ds.add(d)
    deps[m]=ds
def olean(m): return os.path.join(MP,'Outputs/oleans/liquidTensorExperiment/LiquidTensorExperiment',*[s2p(c) for c in m.split('.')])+'.olean'
status={}; lock=threading.Lock(); cv=threading.Condition(lock)
def run(m):
    t=time.time()
    if os.path.exists(olean(m)):
        with cv: status[m]='ok'; cv.notify_all()
        return
    with open(os.path.join(LOG,m+'.log'),'w') as lf:
        r=subprocess.run([MP+'/.lake/build/bin/mathport','config-lte.json','LiquidTensorExperiment::'+m],cwd=MP,stdout=lf,stderr=subprocess.STDOUT)
    ok= r.returncode==0 and os.path.exists(olean(m))
    with cv:
        status[m]='ok' if ok else f'fail({r.returncode})'; cv.notify_all()
    print(f'{status[m]:10} {time.time()-t:6.0f}s {m}',flush=True)
pending=set(mods); running=set()
with ThreadPoolExecutor(J) as ex:
    with cv:
        while pending or running:
            ready=[m for m in pending if all(status.get(d)=='ok' for d in deps[m])]
            blocked=[m for m in pending if any(d in status and status[d]!='ok' for d in deps[m])]
            for m in blocked: pending.discard(m); status[m]='blocked'; print(f'blocked    {m}',flush=True)
            for m in ready:
                if len(running)>=J: break
                pending.discard(m); running.add(m)
                ex.submit(lambda m=m:(run(m), cv.acquire(), running.discard(m), cv.notify_all(), cv.release()))
            if not ready and not blocked and not running and pending:
                print('DEADLOCK',sorted(pending)[:5]); break
            cv.wait(5)
print('SUMMARY', {s:list(status.values()).count(s) for s in set(status.values())})
