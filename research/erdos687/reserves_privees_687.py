"""Look for longer covers by varying prime rows with few private positions."""
import argparse
import ctypes
import json
from collections import Counter
from pathlib import Path
from random import Random
from time import monotonic

from extensions_semences_687 import first_primes, verify
from prolonger_687 import extended, multi_cover
from reparer_fenetre_687 import read_seed


def search(path, output, library, solver, seconds):
    rng = Random(6875217)
    primes = first_primes(200)
    row = read_seed(path,primes)
    ps = primes[1:]
    m = (row["Y"]-1)//2
    seed = [(a*pow(2,-1,p)-1)%p for a,p in zip(row["residues"][1:],ps)]
    assert verify(200,m,seed,primes) == row["residues"]
    fn = library.improve_cover
    ptr = ctypes.POINTER(ctypes.c_int)
    fn.argtypes = [ctypes.c_int,ctypes.c_int,ptr,ptr,ctypes.c_int,ctypes.c_int,ctypes.c_uint,ptr]
    fn.restype = ctypes.c_int
    n = len(ps)
    arr = ctypes.c_int*n
    deadline = monotonic()+seconds
    attempts = 0
    bank = []
    while monotonic()<deadline:
        width = m+1
        if bank and rng.random()<0.8:
            rs = rng.choice(bank)
        else:
            k = rng.choice([0,1,rng.randrange(-25,26)])
            rs = [(a+k)%p for a,p in zip(seed,ps)]
        rows = [range(a,width,p) for a,p in zip(rs,ps)]
        counts = Counter(t for points in rows for t in points)
        priv = [sum(counts[t]==1 for t in points) for points in rows]
        threshold = rng.choice([2,2,2,3,3,4])
        free = {i for i in range(n) if priv[i]<=threshold}
        if attempts%3:
            free = set(rng.sample(sorted(free),rng.randint(max(1,len(free)//3),len(free))))
        if attempts%5==0 and len(free)>8:
            holes = set(range(width))
            for i,points in enumerate(rows):
                if i not in free:
                    holes.difference_update(points)
            found = multi_cover(ps,rs,sorted(holes),free,solver,30000,3)
        else:
            order = [i for i in range(n) if i not in free]+sorted(free)
            values = arr(*(rs[i] for i in order))
            work = (ctypes.c_int*(4*width+2*n))()
            miss = fn(width,n,arr(*(ps[i] for i in order)),values,n-len(free),
                      rng.choice([3000,8000,16000]),rng.getrandbits(32),work)
            candidate = list(rs)
            for i,a in zip(order,values):
                candidate[i] = a
            if miss<=2 and candidate not in bank:
                bank.append(candidate)
                if len(bank)>160:
                    bank.pop(rng.randrange(25))
            found = candidate if miss==0 else None
        attempts+=1
        if attempts%150==0:
            print("attempts",attempts,"near covers",len(bank),"target",2*width+1,flush=True)
        if found is not None:
            seed,m = extended(ps,found,width)
            normal = verify(200,m,seed,primes)
            result = {"200":{"x":1223,"Y":2*m+1,"residues":normal}}
            tmp = output.with_suffix(".tmp")
            tmp.write_text(json.dumps(result)+"\n",encoding="utf-8")
            tmp.replace(output)
            print("verified Y(1223) >=",2*m+1,flush=True)
            bank.clear()


if __name__ == "__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    for key in ["seed","output","library","solver"]:
        cli.add_argument(key,type=Path)
    cli.add_argument("--seconds",type=int,default=3600)
    args=cli.parse_args()
    search(args.seed,args.output,ctypes.CDLL(str(args.library.resolve())),args.solver,args.seconds)
