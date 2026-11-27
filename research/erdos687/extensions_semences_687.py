"""Extend Weeks's finite interval certificates across prime cutoffs.

Coordinates t describe the even positions 2(t+1) of [1,2m+1].
The class 1 modulo 2 already covers all odd positions.
"""
import argparse
import json
from math import isqrt
from pathlib import Path
from zipfile import ZipFile


def first_primes(count):
    size = max(32, 16 * count)
    while True:
        keep = bytearray([1]) * (size + 1)
        for p in range(2, isqrt(size) + 1):
            if keep[p]:
                keep[p*p::p] = bytes(len(range(p*p, size+1, p)))
        primes = [p for p in range(2, size + 1) if keep[p]]
        if len(primes) >= count:
            return primes[:count]
        size *= 2


def uncovered(lo, hi, primes, residues):
    board = bytearray([1]) * (hi - lo)
    for p, r in zip(primes, residues):
        start = (r-lo) % p
        board[start::p] = bytes(len(range(start, len(board), p)))
    return [lo+i for i, b in enumerate(board) if b]


def extend(m, ps, rs, fresh):
    # For each split of the fresh primes, cover the nearest holes on each
    # side. Leave the next hole on each side immediately outside the interval.
    n = len(fresh)
    reach = max(64, 8 * (n + 1))
    while True:
        left = uncovered(-reach, 0, ps, rs)[::-1]
        right = uncovered(m, m+reach, ps, rs)
        if min(len(left), len(right)) > n:
            break
        reach *= 2
    width = lambda k: right[n-k]-left[k]-1
    split = max(range(n+1), key=width)
    shift = left[split]+1
    extra = left[:split] + right[:n-split]
    residues = [(r-shift) % p for r,p in zip(rs,ps)]
    residues.extend((t-shift) % p for t,p in zip(extra,fresh))
    return width(split), residues


def recover(m, ps, rs, fresh, old_width):
    """Take the best window using the first rows of a larger source cover."""
    margin = max(32, 8*(len(fresh)+1))
    lo, hi = -margin, m+margin
    holes = [lo-1, *uncovered(lo,hi,ps,rs), hi]
    stride = min(len(fresh)+1, len(holes)-1)
    i = max(range(len(holes)-stride), key=lambda j: holes[j+stride]-holes[j])
    start = holes[i]+1
    width = holes[i+stride]-start
    if width <= old_width:
        return None
    new = [(r-start) % p for p,r in zip(ps,rs)]
    required = holes[i+1:i+stride]
    new.extend((t-start) % p for p,t in zip(fresh,required))
    new.extend([0]*(len(fresh)-len(required)))
    return width,new


def seed_rows(path, primes):
    prefix = "jacobsthal_Oct292026/anc/"
    with ZipFile(path) as z:
        rows = json.loads(z.read(prefix+"certificates.json"))
        rows.extend(json.loads(z.read(prefix+"catalog/h65_extensions.json")))
        newer = json.loads(z.read(prefix+"method5b_lower_bound_certificates.json"))
    for e in newer["certificates"]:
        k = e["index"]
        a = int(e["coprime_x"])
        rs = [(-a*pow(2,-1,p)-1) % p for p in primes[1:k]]
        rows.append(dict(index=k, gap=e["lower_bound"], odd_residues=rs))
    return rows


def verify(k, m, rs, primes):
    ps = primes[:k]
    assert len(rs) == k-1 and all(0 <= r < p for r,p in zip(rs,ps[1:]))
    assert not uncovered(0, m, ps[1:], rs)
    # Independently check the usual integer interval, including both endpoints.
    normal = [1, *[2*(r+1) % p for p,r in zip(ps[1:],rs)]]
    assert not uncovered(1, 2*m+2, ps, normal)
    return normal


def search(archive, output, cap):
    primes = first_primes(max(cap, 200))
    seeds = seed_rows(archive, primes)
    by_index = {}
    for row in seeds:
        k = row["index"]
        if k <= cap:
            group = by_index.setdefault(k, [])
            m = row["gap"]//2-1
            rs = row["odd_residues"]
            verify(k, m, rs, primes)
            if (m,rs) not in group:
                group.append((m,rs))
    notes = {}
    targets = sorted(by_index)
    # Keep original larger seeds available for downwards interpolation.
    original_rows = {k:max(group) for k,group in by_index.items()}
    for i,k in enumerate(targets):
        group = by_index[k]
        best, _ = max(group)
        original = best
        champion = None
        new_rows = []
        for j in targets[:i]:
            # Each previous index includes its own strongest new extension.
            for m,rs in by_index[j]:
                w,new = extend(m,primes[1:j],rs,primes[j:k])
                if w > best:
                    best = w
                    champion = (j,new)
                    new_rows.append((w,new))
        for j,(m,rs) in original_rows.items():
            if j <= k or j > 4*k:
                continue
            for t in sorted({k-d for d in (0,1,2,3,4,5,7,9,12,16,24,32,k//4,k//2) if k-d>=2}):
                found = recover(m,primes[1:t],rs[:t-1],primes[t:k],best)
                if found is not None:
                    best,new = found
                    champion = (j,new)
                    new_rows.append((best,new))
        if champion is not None:
            j,rs = champion
            normal = verify(k,best,rs,primes)
            # Retain distinct high-quality predecessors. A shorter central
            # cover may have a much better distribution of exterior holes.
            by_index[k].extend(new_rows[-4:])
            notes[str(k)] = dict(x=primes[k-1],Y=2*best+1,source_index=j,
                                 published_table_Y=2*original+1,residues=normal)
            print(k, primes[k-1], 2*original+1, 2*best+1, "from", j, flush=True)
        # Subsequent runs can independently verify the records accumulated so far.
        tmp = output.with_suffix(".tmp")
        tmp.write_text(json.dumps(notes,separators=(",",":"))+"\n",encoding="utf-8")
        tmp.replace(output)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("archive",type=Path)
    cli.add_argument("output",type=Path)
    cli.add_argument("--cap",type=int,default=1070)
    args=cli.parse_args()
    search(args.archive,args.output,args.cap)
