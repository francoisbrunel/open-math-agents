"""Generate plain Lean kernel proofs from full-cover witnesses in JSON."""
import argparse
import json
from pathlib import Path

from extensions_semences_687 import first_primes


def crt(primes, residues):
    a, modulus = 0, 1
    for p, r in zip(primes, residues, strict=True):
        a += modulus * ((r-a)*pow(modulus,-1,p) % p)
        modulus *= p
    assert all(a % p == r for p,r in zip(primes,residues))
    return a


def declaration(k, data, primes, chunk_size=0):
    x, h = data["x"], data["Y"]
    residues = data["residues"]
    assert len(primes) == len(residues) and primes[-1] == x
    a = crt(primes,residues)
    witnesses = [0]*(h+1)
    for p,r in reversed(list(zip(primes,residues))):
        for n in range(r,h+1,p):
            witnesses[n] = p
    assert all(2<=d<=x and (n-a)%d == 0 for n,d in enumerate(witnesses) if n)
    bits = x.bit_length()
    words = [sum(d << (j*bits) for j,d in enumerate(witnesses[i:i+64]))
             for i in range(0,h+1,64)]
    # Each column selects a nontrivial divisor. Primality need not be trusted.
    lines = [f"namespace At{k}",f"private def residue : Nat := {hex(a)}",
             "private def words : Array Nat := #[",
             ",\n".join(hex(w) for w in words)+"]",
             f"private def witness := entry words {bits}"]
    if chunk_size:
        lines=lines[:2]
        parts=[]
        for lo in range(1,h+1,chunk_size):
            hi=min(h+1,lo+chunk_size)
            digits=sum(d << (j*bits) for j,d in enumerate(witnesses[lo:hi]))
            lines.append(f"private theorem s{lo} : Slice {x} residue {lo} {hi} := "+
                         f"slice (len := {hi-lo}) (word := {digits:#x}) (bits := {bits}) (by decide +kernel)")
            parts.append(f"s{lo}")
        while len(parts)>1:
            joined=[f"(appendSlice {parts[i]} {parts[i+1]})" for i in range(0,len(parts)-1,2)]
            if len(parts)%2:
                joined.append(parts[-1])
            parts=joined
        lines.append(f"theorem certificate : Window {x} {h} := window_of_slice {parts[0]}")
    else:
        lines.extend([f"theorem certificate : Window {x} {h} := by",
                      "  apply assemble (a := residue) (w := witness)","  decide"])
    lines.extend([f"end At{k}",f"#print axioms At{k}.certificate",""])
    return "\n".join(lines)


def generate(data, indices, namespace="CertificatsSemences687", chunk_size=0):
    if chunk_size<0:
        raise ValueError("Chunk size must be nonnegative")
    if not namespace.isascii() or not namespace.isidentifier():
        raise ValueError("Expected one Lean namespace identifier")
    primes = first_primes(max(indices))
    parts = ["import TemoinIntervalle687","namespace "+namespace,
             "open TemoinIntervalle687","set_option maxRecDepth 32768",
             "set_option maxHeartbeats 16000000",""]
    parts.extend(declaration(k,data[str(k)],primes[:k],chunk_size) for k in indices)
    return "\n".join(parts)+"\nend "+namespace+"\n"


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("json",type=Path)
    cli.add_argument("output",type=Path)
    cli.add_argument("indices",nargs="*",type=int)
    cli.add_argument("--namespace",default="CertificatsSemences687")
    cli.add_argument("--chunk-size",type=int,default=0)
    args = cli.parse_args()
    data = json.loads(args.json.read_text(encoding="utf-8"))
    args.output.write_text(generate(data,args.indices or sorted(map(int,data)),args.namespace,args.chunk_size),encoding="utf-8")
