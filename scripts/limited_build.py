#!/usr/bin/env python3
"""Fair two-slot queue for heavyweight Lean invocations; no proof semantics changed."""
import fcntl,os,pathlib,subprocess,sys,time
root=pathlib.Path(os.environ.get('CGLMP5_BUILD_LOCK_DIR','/tmp/cglmp5-lean-heavy-slots'))
root.mkdir(exist_ok=True,parents=True); queue=root/'queue';queue.mkdir(exist_ok=True)
guard=open(root/'queue.lock','a+');slots=[open(root/f'slot{i}.lock','a+') for i in range(2)]
fcntl.flock(guard,fcntl.LOCK_EX)
try:
 counter=root/'counter';ticket=int(counter.read_text())+1 if counter.exists() else 1;counter.write_text(str(ticket))
 request=queue/f'{ticket:012d}.request';request_fd=open(request,'w+');fcntl.flock(request_fd,fcntl.LOCK_EX);request_fd.write(' '.join(sys.argv[1:]));request_fd.flush()
finally:fcntl.flock(guard,fcntl.LOCK_UN)
try:
 while True:
  chosen=None
  fcntl.flock(guard,fcntl.LOCK_EX)
  try:
   # Reap abandoned requests through OS-held locks, never guessed process IDs.
   for p in sorted(queue.glob('*.request')):
    if p==request:continue
    with open(p,'a+') as f:
     try:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
     except BlockingIOError:continue
     p.unlink(missing_ok=True)
   waiting=sorted(queue.glob('*.request'))
   if waiting and waiting[0]==request:
    for i,f in enumerate(slots):
     try:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
     except BlockingIOError:continue
     chosen=(i,f);request.unlink(missing_ok=True);break
  finally:fcntl.flock(guard,fcntl.LOCK_UN)
  if chosen:
   i,f=chosen;print(f'[limited-build] ticket{ticket} acquired slot{i}: '+' '.join(sys.argv[1:]),flush=True)
   try:sys.exit(subprocess.call(sys.argv[1:]))
   finally:fcntl.flock(f,fcntl.LOCK_UN)
  time.sleep(.2)
finally:
 request.unlink(missing_ok=True)
 fcntl.flock(request_fd,fcntl.LOCK_UN)
