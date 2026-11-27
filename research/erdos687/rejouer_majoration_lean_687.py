"""Generate ordinary-kernel Lean replay modules for unbranched interval cores."""
import argparse
import base64
import gzip
import json
from math import gcd, isqrt, prod
from pathlib import Path
import zlib


def prime_list(x):
    return [p for p in range(2, x+1) if all(p%d for d in range(2,isqrt(p)+1))]


def encode_record(rec, primes):
    cutoff = rec["base"]
    if primes[cutoff-1] != 17 or len(rec["weights"]) != 1:
        raise ValueError("Expected an unbranched wheel through 17")
    period = prod(primes[:cutoff])
    lo, last, high = rec["b"], rec["last"], rec["b"]+rec["H"]
    L, N = period+last+1, high-last
    size, encoded = rec["weights"][0]
    buf = zlib.decompress(base64.b64decode(encoded, validate=True))
    if size not in (1,2) or len(buf)%size:
        raise ValueError("Invalid weight width")
    points = (n for n in range(lo+rec["slack"]+1, high+1) if gcd(n,period)==1)
    weights = (int.from_bytes(buf[i:i+size],"little") for i in range(0,len(buf),size))
    active = [(n-last-1,w) for n,w in zip(points,weights,strict=True) if n>last and w]
    packed = bytearray(4*N)
    for i,w in active:
        packed[4*i:4*i+4] = w.to_bytes(4, "little")
    caps = [0]*cutoff
    for p in primes[cutoff:]:
        bins = [0]*p
        for i,w in active:
            bins[i%p] += w
        caps.append(max(bins))
    if sum(w for _,w in active)<=sum(caps):
        raise ValueError("Nonpositive margin")
    return L, N, int.from_bytes(packed, "little"), caps


def generate(path, output, first, count):
    opener = gzip.open if path.suffix == ".gz" else open
    output.mkdir(parents=True, exist_ok=True)
    with opener(path,"rt",encoding="utf-8") as file:
        for idx,line in enumerate(file):
            if idx<first:
                continue
            if idx>=first+count:
                break
            rec = json.loads(line)
            primes = prime_list(rec["x"])
            modulus = prod(primes[:rec["base"]])
            L,N,F,caps = encode_record(rec,primes)
            name = f"Core{rec['x']}H{rec['H']}N{idx}"
            source = f"""import NoyauPondere687

namespace {name}
open NoyauPondere687

set_option maxRecDepth 20000
set_option exponentiation.threshold 500000
set_option maxHeartbeats 0

private def weights : ℕ := {F:#x}
private def rows : List (ℕ × ℕ) := List.zip {primes} {caps}

theorem certified : Obstruction {L} {N} {primes} :=
  sound (F := weights) (rows := rows) (by decide +kernel)

theorem starts : ∀ b : ℕ, {modulus+rec["b"]} ≤ b → b ≤ {modulus+rec["last"]} →
    b+1 ≤ {L} ∧ {L}+{N} ≤ b+{rec["H"]}+1 := by omega

#print axioms certified
end {name}
"""
            (output/(name+".lean")).write_text(source, encoding="utf-8")


def join_tree(leaves):
    while len(leaves)>1:
        pairs = [f"(join {leaves[j]} {leaves[j+1]})" for j in range(0,len(leaves)-1,2)]
        if len(leaves)%2:
            pairs.append(leaves[-1])
        leaves=pairs
    return leaves[0]


def full_replay(path, output, group_size):
    if group_size<1:
        raise ValueError("A group must contain at least one record")
    opener=gzip.open if path.suffix==".gz" else open
    with opener(path,"rt",encoding="utf-8") as file:
        records=[json.loads(line) for line in file]
    if not records:
        raise ValueError("Empty certificate")
    x,H=records[0]["x"],records[0]["H"]
    primes=prime_list(x)
    period=prod(primes[:7])
    wheel=f"Wheel{x}H{H}"
    output.mkdir(parents=True,exist_ok=True)
    def write(name,source):
        (output/(name+".lean")).write_text(source,encoding="utf-8")
    write(wheel, f"import VerificationPoids687\nnamespace {wheel}\ndef primes : List Nat := {primes}\nend {wheel}\n")
    previous=-(H+1)//2-1
    first=period+previous+1
    chunks=[]
    for j in range(0,len(records),group_size):
        subset=records[j:j+group_size]
        name=f"{wheel}Group{j//group_size:03d}"
        doc=[f"import {wheel}",f"namespace {name}",f"open {wheel} VerificationPoids687",
             "set_option maxRecDepth 20000","set_option exponentiation.threshold 500000",
             "set_option maxHeartbeats 0"]
        leaves=[]
        for idx,rec in enumerate(subset,j):
            if (rec["x"],rec["H"],rec["b"])!=(x,H,previous+1):
                raise ValueError("Nonconsecutive or mixed-parameter certificates")
            previous=rec["last"]
            L,N,F,caps=encode_record(rec,primes)
            doc.extend([f"private def w{idx} : Nat := {F:#x}",
                        f"private def q{idx} : List (Nat × Nat) := primes.zip {caps}",
                        f"private theorem e{idx} : Encoded {L} {N} primes := " +
                        f"⟨w{idx},q{idx},rfl,by decide +kernel⟩",
                        f"private theorem s{idx} : Segment primes {H} {period+rec['b']} {period+previous} := "+
                        f"leaf (by decide) (by decide) e{idx}"])
            leaves.append(f"s{idx}")
        doc.extend([f"theorem certified : Segment primes {H} {period+subset[0]['b']} {period+previous} := "+
                    join_tree(leaves),"#print axioms certified",f"end {name}"])
        write(name,"\n".join(doc)+"\n")
        chunks.append(name)
    if previous+period<first+period//2:
        raise ValueError("Incomplete canonical phases")
    doc=[*(f"import {chunk}" for chunk in chunks),f"namespace {wheel}", "open VerificationPoids687",
         f"theorem certified : Segment primes {H} {first} {period+previous} := "+
         join_tree([chunk+".certified" for chunk in chunks]),"#print axioms certified",f"end {wheel}"]
    write(wheel+"Full","\n".join(doc)+"\n")
    if (x,H)==(863,6890):
        write("Borne863Finale",f"""import {wheel}Full
import Phases687
namespace Borne863Finale
open {wheel} Phases687
set_option maxRecDepth 20000
theorem bound : Erdos687.Y 863 < 6890 := by
  have same : primes.toFinset = (863:ℕ).primesLE := by decide +kernel
  have hp (p : ℕ) : p ∈ primes ↔ p≤863 ∧ p.Prime := by
    rw [← List.mem_toFinset,same,Nat.mem_primesLE]
  apply wheel6890 hp
  intro t lo hi a norm
  obtain ⟨L,N,hL,hN,proof⟩ := certified t lo (hi.trans (by decide))
  exact core_excludes (fun p h => ((hp p).mp h).2.pos) hL hN (NoyauPondere687.encoded proof) norm
#print axioms bound
end Borne863Finale
""")
    return [wheel,*chunks,wheel+"Full"]


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate",type=Path)
    parser.add_argument("destination",type=Path)
    parser.add_argument("--first",type=int,default=0)
    parser.add_argument("--count",type=int,default=1)
    parser.add_argument("--full",action="store_true")
    parser.add_argument("--group-size",type=int,default=12)
    args=parser.parse_args()
    if args.full:
        full_replay(args.certificate,args.destination,args.group_size)
    else:
        generate(args.certificate,args.destination,args.first,args.count)
