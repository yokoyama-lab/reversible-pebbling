import ast, datetime, hashlib, itertools, json, pathlib, re, sys, time
srcpath=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2]); out.mkdir(exist_ok=True)
src=srcpath.read_bytes(); assert hashlib.sha256(src).hexdigest()=='ab087e2a09ad672be9248e409381581905e98fa0635cae3b111a65a1c06fa9cf'
start=datetime.datetime.now(datetime.timezone.utc).isoformat(); tick=time.monotonic(); results={}; details={}
for name in ['I','M']:
 s=src.decode().split('namespace '+name+'\n')[1]
 events=[(b=='true',int(v)) for b,v in re.findall(r'⟨(false|true), (\d+)⟩',re.search(r'def events .*? := (.*)',s)[1])]
 def arr(k): return ast.literal_eval(re.search(r'def '+k+r' .*? := (.*)',s)[1])
 initial=arr('initial'); final=arr('final'); erasures=arr('erasures'); n=len(events)
 def enumerate_physical(capacity):
  words=[]
  def visit(prefix,board,used):
   if len(prefix)==n:
    if len(board)==len(final) and all(x in final for x in board): words.append(tuple(prefix))
    return
   for i,(place,v) in enumerate(events):
    if used>>i&1: continue
    pred=v==1 or max(v-1,0) in board
    if place:
     if v in board or not pred: continue
     after=[v]+board
    else:
     if v not in board or ((not pred)!=(v in erasures)): continue
     after=board.copy();after.remove(v)
    if capacity and len(after)>5: continue
    visit(prefix+[i],after,used|(1<<i))
  visit([],initial,0);return set(words)
 legal=enumerate_physical(True); noncap=enumerate_physical(False)
 Q={(a,b) for a in range(n) for b in range(n) if a!=b and all(w.index(a)<w.index(b) for w in legal)}
 assert legal and all((b,a) not in Q for a,b in Q)
 pred={b:{a for a,c in Q if c==b} for b in range(n)}; extensions=set()
 def topo(prefix,used):
  if len(prefix)==n:extensions.add(tuple(prefix));return
  for i in range(n):
   if i not in used and pred[i]<=used:topo(prefix+[i],used|{i})
 topo([],set())
 def guard(w):
  h=len(initial)
  for i in w:
   h+=1 if events[i][0] else -1
   if not 0<=h<=5:return False
  return True
 guarded={w for w in extensions if guard(w)}
 a=sorted(extensions-noncap);b=sorted(noncap-extensions)
 results[name]={'capacity_legal_count':len(legal),'noncapacity_legal_count':len(noncap),'Q_extension_count':len(extensions),'Q_edges':len(Q),'Q_not_noncapacity_count':len(a),'noncapacity_not_Q_count':len(b),'Q_not_noncapacity_first':a[:1],'noncapacity_not_Q_first':b[:1],'guarded_Q_equals_capacity':guarded==legal,'equivalence':extensions==noncap}
 details[name]={'events':events,'initial':initial,'final':final,'erasures':erasures,'Q':sorted(Q),'Q_not_noncapacity':a,'noncapacity_not_Q':b}
result={'start':start,'stop':datetime.datetime.now(datetime.timezone.utc).isoformat(),'wall_seconds':time.monotonic()-tick,'source_sha':hashlib.sha256(src).hexdigest(),'results':results,'scope':'New converse-equivalence/difference audit; Python ordered-list translation of original step, not Lean verification. Reconstructed Q from all capacity words, not witnesses.'}
(out/'RESULT.json').write_text(json.dumps(result,indent=2));(out/'DETAILS.json').write_text(json.dumps(details,indent=2));print(json.dumps(result))
