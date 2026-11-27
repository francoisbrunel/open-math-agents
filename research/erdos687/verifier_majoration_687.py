"""Independent exact replay of interval exclusions. Python standard library only."""
import argparse
import base64
import gzip
from itertools import zip_longest
import json
from math import isqrt, prod
from pathlib import Path
import zlib


def is_prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))


def check(path,H=6890,cutoff=863,base=17):
    primes=[p for p in range(2,cutoff+1) if is_prime(p)]
    small=[p for p in primes if p<=base]
    large=[p for p in primes if p>base]
    period=prod(small)
    # Every possible start modulo the wheel must have a direct or reflected
    # obstruction. Record them explicitly, independently of the generator.
    forbidden=bytearray(period)
    records=0
    before=None
    smallest=None
    open_certificate = gzip.open if path.suffix == ".gz" else open
    with open_certificate(path, mode="rt", encoding="utf-8") as f:
        for line in f:
            rec=json.loads(line)
            lo,end=rec["b"],rec["last"]
            if rec["H"]!=H or rec["x"]!=cutoff or rec["base"]!=len(small):
                raise ValueError("Unexpected parameters")
            if before is not None and lo!=before+1:
                raise ValueError("Discontinuous certificate segments")
            if not lo<=end<lo+H or not 0<=rec["slack"]<H:
                raise ValueError("Invalid core")
            before=end
            entries=rec["weights"]
            if len(entries)==1:
                phases=[None]; tail=large
            elif len(entries)==large[0]:
                phases=list(range(large[0]));tail=large[1:]
            else:
                raise ValueError("Missing residue branches")
            for omitted,(size,enc) in zip(phases,entries,strict=True):
                if size not in (1,2):
                    raise ValueError("Invalid integer width")
                buf=zlib.decompress(base64.b64decode(enc,validate=True))
                candidates=(n for n in range(lo+rec["slack"]+1,lo+H+1)
                            if all(n%p for p in small) and
                            (omitted is None or n%large[0]!=omitted))
                weights=(int.from_bytes(buf[j:j+size],"little") for j in range(0,len(buf),size))
                if len(buf)%size:
                    raise ValueError("Byte length mismatch")
                weighted={}
                for n,w in zip_longest(candidates,weights):
                    if n is None or w is None:
                        raise ValueError("Weight count mismatch")
                    if n>end and w:
                        weighted[n]=w
                # This intersection is contained in every window whose
                # left endpoint is in [lo,end]. Each row gets one class.
                total=sum(weighted.values())
                budget=0
                for p in tail:
                    sums={}
                    for n,w in weighted.items():
                        r=n%p
                        sums[r]=sums.get(r,0)+w
                    budget+=max(sums.values(),default=0)
                if total<=budget:
                    raise ValueError(f"No strict weight obstruction at {lo}, branch {omitted}")
                margin=total-budget
                smallest=margin if smallest is None else min(smallest,margin)
            for b in range(lo,end+1):
                forbidden[b%period]=1
                forbidden[(-b-H-1)%period]=1
            records+=1
    return records,sum(forbidden),period,smallest


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("path",type=Path)
    cli.add_argument("--length",type=int,default=6890)
    cli.add_argument("--cutoff",type=int,default=863)
    cli.add_argument("--base",type=int,default=17)
    args=cli.parse_args()
    num,done,total,margin=check(args.path,args.length,args.cutoff,args.base)
    print("Complete" if done==total else "Partial",
          f"{done}/{total} phases; {num} certificates; least integer margin {margin}")
    raise SystemExit(0 if done == total else 1)
