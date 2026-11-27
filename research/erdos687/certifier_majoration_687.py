"""Search and replay integer weighted exclusions on translated prime wheels."""
import argparse
import base64
import ctypes
import json
from math import gcd, prod
from pathlib import Path
from time import monotonic
import zlib

from extensions_semences_687 import first_primes


def points(lo, length, period, skip, extra):
    return [n for n in range(lo+1,lo+length+1)
            if gcd(n,period)==1 and (skip is None or n%extra!=skip)]


def packed(weights):
    size=1 if max(weights)<256 else 2
    raw=b"".join(int(w).to_bytes(size,"little") for w in weights)
    return [size,base64.b64encode(zlib.compress(raw,6)).decode("ascii")]


def unpack(row):
    size,data=row
    if size not in (1,2):
        raise ValueError("Invalid weight encoding")
    raw=zlib.decompress(base64.b64decode(data,validate=True))
    if len(raw)%size:
        raise ValueError("Incomplete weight")
    return [int.from_bytes(raw[i:i+size],"little") for i in range(0,len(raw),size)]


def last_start(lo,pos,weights,primes):
    """Integer arithmetic. Each new prime can remove at most its heaviest class."""
    assert len(pos)==len(weights)
    total=sum(weights)
    margin=total
    for p in primes:
        mass=[0]*p
        for n,w in zip(pos,weights):
            mass[n%p]+=w
        margin-=max(mass)
    if margin<=0:
        return lo-1
    # All smaller deletions of a left prefix preserve strict separation.
    for n,w in zip(pos,weights):
        margin-=w
        if margin<=0:
            return n-1
    raise ValueError("A positive witness needs nonempty support")


def validate(rec,b,H,ps,s):
    period=prod(ps[:s])
    assert rec["b"]==b and rec["H"]==H and rec["x"]==ps[-1] and rec["base"]==s
    slack=rec["slack"]
    assert 0<=slack<H
    lo=b+slack
    pack=rec["weights"]
    assert len(pack) in (1,ps[s])
    branches=len(pack)>1
    last=b+H
    for i,row in enumerate(pack):
        skip=i if branches else None
        pos=points(lo,H-slack,period,skip,ps[s])
        last=min(last,last_start(lo,pos,unpack(row),ps[s+int(branches):]))
    assert last>=lo and last==rec["last"]
    return last+1


def replay(path,k,H,s):
    ps=first_primes(k)
    start=-(H+1)//2
    b=start
    with path.open(encoding="utf-8") as f:
        for line in f:
            b=validate(json.loads(line),b,H,ps,s)
    end=start+prod(ps[:s])//2
    return b,end


class Search:
    def __init__(self,library):
        import numpy as np
        self.np=np
        ptr=ctypes.POINTER
        self.lib=ctypes.CDLL(str(library.resolve())).search_weights
        self.lib.argtypes=[ctypes.c_int,ctypes.c_int,ptr(ctypes.c_int),ptr(ctypes.c_int),
                           ctypes.c_int,ctypes.c_double,ptr(ctypes.c_double)]
        self.lib.restype=ctypes.c_double
        self.cache={}

    def fit(self,ps,s,b,H,slack,skip,iters):
        np=self.np
        lo=b+slack
        pos=np.array(points(lo,H-slack,prod(ps[:s]),skip,ps[s]),dtype=np.int32)
        new=np.array(ps[s+int(skip is not None):],dtype=np.int32)
        w=np.ones(len(pos))
        if skip in self.cache:
            old,prior=self.cache[skip]
            j=np.searchsorted(old,pos)
            use=np.nonzero(j<len(old))[0]
            use=use[old[j[use]]==pos[use]]
            w[use]=prior[j[use]]
        def addr(arr,type_):
            return arr.ctypes.data_as(ctypes.POINTER(type_))
        ratio=self.lib(len(pos),len(new),addr(new,ctypes.c_int),addr(pos,ctypes.c_int),
                       iters,.9994,addr(w,ctypes.c_double))
        self.cache[skip]=(pos,w.copy())
        if ratio>=1:
            return None
        # Round to a finite certificate. Only the subsequent integer test counts.
        norm=w/w.max()
        positions=pos.tolist()
        for scale in (32,128,255,2048,65535):
            integer=np.rint(scale*norm).astype(np.int64).tolist()
            last=last_start(lo,positions,integer,new.tolist())
            if last>=lo:
                return last,packed(integer)
        return None


def search(path,k,H,s,library,seconds):
    ps=first_primes(k)
    period=prod(ps[:s])
    start=-(H+1)//2
    b,end=replay(path,k,H,s) if path.exists() else (start,start+period//2)
    engine=Search(library)
    deadline=monotonic()+seconds
    count=0
    with path.open("a",encoding="utf-8") as dest:
        while b<=end and monotonic()<deadline:
            found=None
            for slack,extra,iters in [(240,False,650),(150,False,1000),(70,False,1400),
                                      (220,True,560),(100,True,800),(20,True,1500),(0,True,2800)]:
                rows=[]
                last=b+H
                for skip in range(ps[s]) if extra else [None]:
                    result=engine.fit(ps,s,b,H,slack,skip,iters)
                    if result is None:
                        break
                    far,row=result
                    last=min(last,far)
                    rows.append(row)
                else:
                    found=dict(b=b,H=H,x=ps[-1],base=s,slack=slack,last=last,weights=rows)
                    break
            if found is None:
                print("Uncertified coordinate",b,flush=True)
                break
            dest.write(json.dumps(found,separators=(",",":"))+"\n")
            dest.flush()
            b=found["last"]+1
            count+=1
            if count%50==0 or b>end:
                print("phase positions certified",b-start,"of",end-start+1,"new entries",count,flush=True)
    print("Finished" if b>end else "Partial",b-start,"of",end-start+1,flush=True)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("output",type=Path)
    cli.add_argument("--k",type=int,default=150)
    cli.add_argument("--length",type=int,default=6890)
    cli.add_argument("--base",type=int,default=7)
    cli.add_argument("--library",type=Path)
    cli.add_argument("--seconds",type=int,default=5400)
    args=cli.parse_args()
    if args.library:
        search(args.output,args.k,args.length,args.base,args.library,args.seconds)
    else:
        b,end=replay(args.output,args.k,args.length,args.base)
        print("Complete" if b>end else "Partial",b,end)
