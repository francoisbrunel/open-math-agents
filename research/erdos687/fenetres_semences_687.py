"""Test neighboring windows of the Weeks seeds for a complete cover."""
import argparse
from bisect import bisect_left
import heapq
import json
from pathlib import Path
from random import Random
from time import monotonic

from extensions_semences_687 import first_primes, seed_rows, uncovered, verify
from prolonger_687 import extended, multi_cover


def local_windows(m, width, ps, rs, radius, rng, take=7):
    start = -radius
    end = max(0,m-width)+radius
    holes = uncovered(start,end+width,ps,rs)
    choices = {start,end,0,m-width}
    # Sliding the left endpoint changes the window's residual set only as an
    # uncovered point enters at the right or disappears on the left.
    for h in holes:
        if start<=h+1<=end:
            choices.add(h+1)
        if start<=h-width+1<=end:
            choices.add(h-width+1)
    ranked=[]
    visited=set()
    for left in sorted(choices):
        lo=bisect_left(holes,left)
        hi=bisect_left(holes,left+width)
        if (lo,hi) not in visited:
            ranked.append((hi-lo,rng.random(),left,lo,hi))
            visited.add((lo,hi))
    for _,_,left,lo,hi in heapq.nsmallest(take,ranked):
        yield left,[h-left for h in holes[lo:hi]]


def run(archive, solver, output, imports, seconds):
    primes=first_primes(200)
    groups={k:[] for k in (100,150,200)}
    for row in seed_rows(archive,primes):
        k=row["index"]
        if k in groups:
            groups[k].append((row["gap"]//2-1,row["odd_residues"]))
    for path in [*imports,output]:
        if not path.exists():
            continue
        for idx,rec in json.loads(path.read_text()).items():
            k=int(idx)
            if k in groups:
                r=[(a*pow(2,-1,p)-1)%p for a,p in zip(rec["residues"][1:],primes[1:k])]
                groups[k].append(((rec["Y"]-1)//2,r))
    best={k:max(m for m,r in rows) for k,rows in groups.items()}
    records=json.loads(output.read_text()) if output.exists() else {}
    seen=set()
    repeats=0
    rng=Random(687213)
    end=monotonic()+seconds
    attempts=0
    while monotonic()<end:
        k=rng.choice(list(groups))
        source=rng.choice([k,k,*groups])
        m,rs=rng.choice(groups[source])
        width=best[k]+rng.choice([1,1,1,2,3,4])
        if m<width//2:
            continue
        count=rng.choice([4,5,6,7,8,10,12,15,18,21,25,30,36,40,46,53,60])
        t=min(k-count,source)
        if t<12:
            continue
        ps=primes[1:k]
        free=set(range(t-1,k-1))
        prefix=rs[:t-1]
        tag=(width,k,t,tuple(prefix))
        if tag in seen:
            repeats+=1
            if repeats>=300:
                seen.clear()
                repeats=0
            continue
        repeats=0
        seen.add(tag)
        for left,holes in local_windows(m,width,ps[:t-1],prefix,3*width,rng,12):
            if len(holes)>3*len(free):
                continue
            init=[(r-left)%p for r,p in zip(prefix,ps)]+[0]*len(free)
            found=multi_cover(ps,init,holes,free,solver,6000,2)
            attempts+=1
            if found is None:
                continue
            rs2,new=extended(ps,found,width)
            normal=verify(k,new,rs2,primes)
            best[k]=new
            groups[k].append((new,rs2))
            records[str(k)]={"x":primes[k-1],"Y":2*new+1,"residues":normal}
            tmp=output.with_suffix(".tmp")
            tmp.write_text(json.dumps(records,separators=(",",":"))+"\n",encoding="utf-8")
            tmp.replace(output)
            print(k,"Y >=",2*new+1,"trials",attempts,flush=True)
            break
        # Once all tuples are consumed, revisit alternative ties in the scan.
        if len(seen)>600:
            seen.clear()
    print("Finished",attempts,"window tests",flush=True)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("archive",type=Path)
    cli.add_argument("solver",type=Path)
    cli.add_argument("output",type=Path)
    cli.add_argument("--include",type=Path,action="append",default=[])
    cli.add_argument("--seconds",type=int,default=1800)
    args=cli.parse_args()
    run(args.archive,args.solver,args.output,args.include,args.seconds)
