"""Search all nearby choices of odd prime classes on a translated window."""
import argparse
import json
from pathlib import Path
from time import monotonic

from extensions_semences_687 import first_primes, verify
from prolonger_687 import extended


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def solve(primes, initial, width, moves, deadline):
    full = (1 << width)-1
    strides = [((1 << (p*((width+p-1)//p)))-1)//((1 << p)-1) for p in primes]
    rows = [(word << a) & full for word,a in zip(strides,initial)]
    # The union over all rows outside a chosen subset is kept in a binary
    # tree, so applying or undoing a change only touches log(k) integers.
    size = 1 << (len(primes)-1).bit_length()
    tree = [0]*(2*size)
    tree[size:size+len(rows)] = rows
    for i in range(size-1,0,-1):
        tree[i] = tree[2*i] | tree[2*i+1]
    chosen = {}
    failed = set()
    visits = 0

    def update(i, mask):
        i += size
        tree[i] = mask
        while i > 1:
            i //= 2
            tree[i] = tree[2*i] | tree[2*i+1]

    def search(left):
        nonlocal visits
        visits += 1
        if visits % 256 == 0 and monotonic() > deadline:
            raise TimeoutError
        holes = full ^ tree[1]
        if holes == 0:
            return [chosen.get(i,r) for i,r in enumerate(initial)]
        if left == 0:
            return None
        key = tuple(sorted(chosen.items()))
        if key in failed:
            return None
        cells = list(positions(holes))
        need = (len(cells)+left-1)//left
        options = []
        for i,p in enumerate(primes):
            if i in chosen:
                continue
            if need == 1:
                candidates = [cells[0] % p]
            elif cells[-1]-cells[0] < (need-1)*p:
                continue
            else:
                counts = {}
                for t in cells:
                    r = t % p
                    counts[r] = counts.get(r,0)+1
                candidates = [r for r,c in counts.items() if c >= need]
            for r in candidates:
                mask = (strides[i] << r) & full
                update(i,mask)
                missing = (full ^ tree[1]).bit_count()
                update(i,rows[i])
                if missing == 0:
                    return [r if j==i else chosen.get(j,a) for j,a in enumerate(initial)]
                if left > 1:
                    options.append((missing,i,r,mask))
        for _,i,r,mask in sorted(options):
            chosen[i] = r
            update(i,mask)
            found = search(left-1)
            if found is not None:
                return found
            update(i,rows[i])
            del chosen[i]
        if len(failed) < 300000:
            failed.add(key)
        return None

    try:
        found = search(moves)
        exhausted = True
    except TimeoutError:
        found,exhausted = None,False
    return found,visits,exhausted


def run(path, out, index, seconds, radius, window):
    primes = first_primes(index)
    record = json.loads(path.read_text(encoding="utf-8"))[str(index)]
    assert record["x"] == primes[-1] and record["residues"][0] == 1
    odd = [(a*pow(2,-1,p)-1)%p for a,p in zip(record["residues"][1:],primes[1:])]
    m = (record["Y"]-1)//2
    assert verify(index,m,odd,primes) == record["residues"]
    # Rank adjacent translates by the number of initially uncovered positions.
    # Every shift in the requested window is still tested.
    shifts = range(-window,window+2)
    starts = {}
    for shift in shifts:
        seed = [(a+shift)%p for a,p in zip(odd,primes[1:])]
        occupancy = bytearray(m+1)
        for p,r in zip(primes[1:],seed):
            occupancy[r::p] = bytes([1])*len(range(r,m+1,p))
        starts[shift] = (occupancy.count(0),seed)
    for depth in range(1,radius+1):
        for shift in sorted(shifts,key=lambda k:(starts[k][0],abs(k),k)):
            seed = starts[shift][1]
            sol,n,done = solve(primes[1:],seed,m+1,depth,monotonic()+seconds)
            print(f"depth={depth} shift={shift} states={n} complete={done} found={sol is not None}",flush=True)
            if sol is not None:
                sol,new_m = extended(primes[1:],sol,m+1)
                residues = verify(index,new_m,sol,primes)
                fresh = {str(index):{"x":primes[-1],"Y":2*new_m+1,"residues":residues}}
                out.write_text(json.dumps(fresh)+"\n",encoding="utf-8")
                return


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("seed",type=Path)
    cli.add_argument("output",type=Path)
    cli.add_argument("--index",type=int,default=200)
    cli.add_argument("--radius",type=int,default=5)
    cli.add_argument("--window",type=int,default=0,help="extra half-window offsets on either side")
    cli.add_argument("--seconds",type=float,default=900,help="per depth and orientation")
    args=cli.parse_args()
    run(args.seed,args.output,args.index,args.seconds,args.radius,args.window)
