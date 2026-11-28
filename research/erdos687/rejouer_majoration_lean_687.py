"""Generate ordinary-kernel Lean replay modules for weighted interval cores."""
import argparse
import base64
import gzip
import json
import re
from math import factorial, gcd, isqrt, prod
from pathlib import Path
import zlib


def weight_literal(hex_digits):
    digits = hex_digits.zfill((len(hex_digits)+255)//256*256)
    chunks = [digits[i:i+256] for i in range(0,len(digits),256)]
    return "weight687% [" + ",".join("0x"+part for part in chunks) + "]"


def chunk_group(source, wheel):
    pattern = r"(?m)^(private def w\w* : Nat := )0x([0-9a-fA-F]+)$"
    updated, count = re.subn(pattern,lambda m:m[1]+weight_literal(m[2]), source)
    if count:
        header = "public import "+wheel+"\n"
        if header not in updated:
            raise ValueError("missing public wheel import")
        updated = updated.replace(header, header+"meta import EntierPoids687\n", 1)
    return updated


def prime_list(x):
    return [p for p in range(2, x+1) if all(p%d for d in range(2,isqrt(p)+1))]


def encode_record(rec, primes, omitted=None):
    cutoff = rec["base"]
    if primes[cutoff-1] != 17:
        raise ValueError("Expected the wheel through 17")
    rows = rec["weights"]
    if omitted is None and len(rows) != 1:
        raise ValueError("A residue of 19 must be selected for a branched record")
    if omitted is not None and (primes[cutoff] != 19 or len(rows) != 19 or not 0 <= omitted < 19):
        raise ValueError("Expected all 19 residue branches")
    period = prod(primes[:cutoff])
    lo, last, high = rec["b"], rec["last"], rec["b"]+rec["H"]
    L, N = period+last+1, high-last
    size, encoded = rows[0 if omitted is None else omitted]
    buf = zlib.decompress(base64.b64decode(encoded, validate=True))
    if size not in (1,2) or len(buf)%size:
        raise ValueError("Invalid weight width")
    points = (n for n in range(lo+rec["slack"]+1, high+1)
              if gcd(n,period)==1 and (omitted is None or n%19 != omitted))
    weights = (int.from_bytes(buf[i:i+size],"little") for i in range(0,len(buf),size))
    active = [(n-last-1,w) for n,w in zip(points,weights,strict=True) if n>last and w]
    packed = bytearray(4*N)
    for i,w in active:
        packed[4*i:4*i+4] = w.to_bytes(4, "little")
    caps = [0]*cutoff
    for p in primes[cutoff + (omitted is not None):]:
        bins = [0]*p
        for i,w in active:
            bins[i%p] += w
        caps.append(max(bins))
    if sum(w for _,w in active)<=sum(caps):
        raise ValueError("Nonpositive margin")
    return L, N, int.from_bytes(packed, "little"), caps


def branched_core(name, rec, primes):
    remaining = [p for p in primes if p != 19]
    lines = ["import NoyauPondere687", "import Mathlib.Tactic.FinCases",
             f"namespace {name}", "open NoyauPondere687",
             "set_option maxRecDepth 20000", "set_option exponentiation.threshold 500000",
             "set_option maxHeartbeats 0", f"private def ps : List Nat := {remaining}"]
    for residue in range(19):
        # The checker uses the offset from the first point of the core.
        omitted = (rec["last"] + 1 + residue) % 19
        L, N, F, caps = encode_record(rec, primes, omitted)
        lines.extend([f"private def w{residue} : Nat := {F:#x}",
                      f"private def rows{residue} : List (Nat × Nat) := ps.zip {caps}",
                      f"private theorem e{residue} : ∃ F rows, rows.map Prod.fst = ps ∧ "
                      f"check F {L} {N} rows = true ∧ "
                      f"PolynomePoids687.digit B (F % (B^19-1)) {residue} = 0 := "
                      f"⟨w{residue}, rows{residue}, rfl, by decide +kernel, by decide +kernel⟩"])
    lines += [f"theorem certified : Obstruction {L} {N} (19 :: {remaining}) := by",
              "  apply branch (by decide : 0 < 19)", "  intro j", "  fin_cases j"]
    lines.extend(f"  · exact e{j}" for j in range(19))
    lines += ["#print axioms certified", f"end {name}"]
    return "\n".join(lines) + "\n"


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
            name = f"Core{rec['x']}H{rec['H']}N{idx}"
            if len(rec["weights"]) > 1:
                (output/(name+".lean")).write_text(branched_core(name,rec,primes),encoding="utf-8")
                continue
            L,N,F,caps = encode_record(rec,primes)
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


def join_tree(leaves, operation="join"):
    while len(leaves)>1:
        pairs = [f"({operation} {leaves[j]} {leaves[j+1]})" for j in range(0,len(leaves)-1,2)]
        if len(leaves)%2:
            pairs.append(leaves[-1])
        leaves=pairs
    return leaves[0]


def catalogue_module(output, wheel, x):
    limit = isqrt(x)
    name = "ListePremiers863" if wheel == "Wheel863H6890" else f"ListePremiers{wheel}"
    (output / (name + ".lean")).write_text(f"""import {wheel}
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

namespace {name}
private def small : List Nat := {prime_list(limit)}
private def factorialLimit : Nat := {factorial(limit)}
private def flag (p : Nat) : Bool :=
  if p ≤ {limit} then small.contains p else decide (p.gcd factorialLimit = 1)

private theorem exact_flag {{p : ℕ}} (le : p ≤ {x}) : flag p = true ↔ p.Prime := by
  by_cases early : p ≤ {limit}
  · have table : ∀ j : Fin {limit+1}, small.contains j.val = true ↔ j.val.Prime := by decide +kernel
    simpa [flag,early] using table ⟨p,by omega⟩
  · have factorial : factorialLimit = Nat.factorial {limit} := by decide +kernel
    simp only [flag,if_neg early,decide_eq_true_eq,factorial]
    change p.Coprime (Nat.factorial {limit}) ↔ _
    constructor
    · intro coprime
      have h := (Nat.coprime_factorial_iff (by omega : p ≠ 1)).mp coprime
      by_contra composite
      have sq := Nat.minFac_sq_le_self (by omega : 0 < p) composite
      nlinarith [show {limit+1} ≤ p.minFac by omega]
    · exact fun prime => prime.coprime_factorial_of_lt (by omega)

set_option maxRecDepth 20000 in
private theorem table_eq : (List.range {x+1}).filter flag = {wheel}.primes := by decide +kernel

theorem catalogue (p : ℕ) : p ∈ {wheel}.primes ↔ p ≤ {x} ∧ p.Prime := by
  rw [← table_eq,List.mem_filter]
  simp only [List.mem_range]
  constructor
  · rintro ⟨le,h⟩
    exact ⟨by omega,(exact_flag (by omega)).mp h⟩
  · rintro ⟨le,h⟩
    exact ⟨by omega,(exact_flag le).mpr h⟩
end {name}
""", encoding="utf-8")
    return name


def catalogue_bridge_863(output):
    wheel = "Wheel863H6890"
    catalogue = catalogue_module(output, wheel, 863)
    (output / "Borne863Finale.lean").write_text(f"""import {wheel}Full
import {catalogue}
import Phases687
namespace Borne863Finale
open {wheel} Phases687
set_option maxRecDepth 20000
theorem bound : Erdos687.Y 863 < 6890 := by
  apply wheel6890 {catalogue}.catalogue
  intro t lo hi a norm
  obtain ⟨L,N,hL,hN,proof⟩ := certified t lo (hi.trans (by decide))
  exact core_excludes (fun p h => (({catalogue}.catalogue p).mp h).2.pos) hL hN (NoyauPondere687.encoded proof) norm
#print axioms bound
end Borne863Finale
""", encoding="utf-8")


def mixed_group(wheel, primes, records, first_index, period):
    name = f"{wheel}Group{first_index:04d}"
    lines = ["module",f"public import {wheel}", f"namespace {name}", f"open {wheel} Branches19_687",
             "set_option maxRecDepth 20000", "set_option exponentiation.threshold 500000",
             "set_option maxHeartbeats 0"]
    leaves = []
    for index, rec in enumerate(records, first_index):
        if len(rec["weights"]) == 1:
            L, N, F, caps = encode_record(rec, primes)
            index19 = primes.index(19)
            reordered = [caps[index19], *caps[:index19], *caps[index19+1:]]
            lines += [f"private def w{index} : Nat := {F:#x}",
                      f"private def q{index} := (19 :: tailPrimes).zip {reordered}",
                      f"private theorem e{index} : Core {L} {N} tailPrimes := "
                      f"Or.inl ⟨w{index},q{index},rfl,by decide +kernel⟩"]
        else:
            branches = []
            for j in range(19):
                omitted = (rec["last"] + 1 + j) % 19
                L, N, F, caps = encode_record(rec, primes, omitted)
                label = f"{index}B{j}"
                lines += [f"private def w{label} : Nat := {F:#x}",
                          f"private def q{label} := tailPrimes.zip {caps}",
                          f"private theorem b{label} : Witness {L} {N} tailPrimes {j} := "
                          f"⟨w{label},q{label},rfl,by decide +kernel,by decide +kernel⟩"]
                branches.append(f"(one b{label})")
            lines += [f"private theorem e{index} : Core {L} {N} tailPrimes := "
                      f"Or.inr {join_tree(branches, 'joinCases')}"]
        lo, hi, H = period + rec["b"], period + rec["last"], rec["H"]
        lines += [f"private theorem s{index} : Segment tailPrimes {H} {lo} {hi} := "
                  f"leaf (by decide) (by decide) e{index}"]
        leaves.append(f"s{index}")
    lo = period + records[0]["b"]
    lines += [f"public theorem certified : Segment tailPrimes {H} {lo} {hi} := {join_tree(leaves)}",
              "#print axioms certified", f"end {name}"]
    return name, chunk_group("\n".join(lines) + "\n", wheel)


def mixed_replay(records, output, group_size):
    x, H = records[0]["x"], records[0]["H"]
    primes = prime_list(x)
    period = prod(primes[:7])
    start = -(H+1)//2
    previous = start-1
    for rec in records:
        if (rec["x"],rec["H"],rec["base"],rec["b"]) != (x,H,7,previous+1):
            raise ValueError("Nonconsecutive or mixed-parameter certificates")
        if not rec["b"] <= rec["last"] < rec["b"] + H or not 0 <= rec["slack"] < H:
            raise ValueError("Invalid interval core")
        previous = rec["last"]
    if previous < start+period//2 or period+start < 0:
        raise ValueError("Incomplete or unsupported wheel range")
    def write(name, source):
        target = output / (name + ".lean")
        temporary = target.with_suffix(".lean.tmp")
        temporary.write_text(source, encoding="utf-8")
        temporary.replace(target)
    wheel = f"Wheel{x}H{H}"
    tail = [p for p in primes if p != 19]
    write(wheel, f"module\npublic import Branches19_687\n@[expose] public section\nnamespace {wheel}\ndef primes : List Nat := {primes}\n"
          f"def tailPrimes : List Nat := {tail}\nend {wheel}\n")
    groups = []
    for i in range(0,len(records),group_size):
        name, source = mixed_group(wheel,primes,records[i:i+group_size],i,period)
        write(name,source)
        groups.append(name)
    base = period+start
    lines = ["module",*(f"public import {g}" for g in groups),f"namespace {wheel}", "open Branches19_687",
             f"public theorem certified : Segment tailPrimes {H} {base} {period+previous} := "
             + join_tree([g+".certified" for g in groups]), "#print axioms certified", f"end {wheel}"]
    write(wheel+"Full","\n".join(lines)+"\n")
    return [wheel,*groups,wheel+"Full",*mixed_bridge(output,wheel,x,H,base,period+previous)]


def mixed_bridge(output, wheel, x, H, base, stop):
    catalogue = catalogue_module(output, wheel, x)
    criterion = f"Critere{x}H{H}"
    final = f"Borne{x}H{H}"
    source = f"""import {catalogue}
import Phases687
namespace {criterion}
open {wheel} Phases687
set_option maxRecDepth 20000
theorem from_certificate (certified : Branches19_687.Segment tailPrimes {H} {base} {stop}) :
    Erdos687.Y {x} < {H} := by
  have perm : (19 :: tailPrimes).Perm primes :=
    (List.perm_middle (a := 19) (l₁ := [2,3,5,7,11,13,17]) (l₂ := primes.drop 8)).symm
  have hp (p : ℕ) : p ∈ (19 :: tailPrimes) ↔ p ≤ {x} ∧ p.Prime :=
    perm.mem_iff.trans ({catalogue}.catalogue p)
  exact mixed_wheel (k := {2*(510510-base)-H-1}) (by decide) (by decide) (by decide) hp certified
#print axioms from_certificate
end {criterion}
"""
    (output / (criterion + ".lean")).write_text(source, encoding="utf-8")
    (output / (final + ".lean")).write_text(f"""import {wheel}Full
import {criterion}
namespace {final}
theorem bound : Erdos687.Y {x} < {H} := {criterion}.from_certificate {wheel}.certified
#print axioms bound
end {final}
""", encoding="utf-8")
    return [catalogue,criterion,final]


def full_replay(path, output, group_size):
    if group_size<1:
        raise ValueError("A group must contain at least one record")
    opener=gzip.open if path.suffix==".gz" else open
    with opener(path,"rt",encoding="utf-8") as file:
        records=[json.loads(line) for line in file]
    if not records:
        raise ValueError("Empty certificate")
    if any(len(rec["weights"]) > 1 for rec in records):
        output.mkdir(parents=True,exist_ok=True)
        return mixed_replay(records,output,group_size)
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
        catalogue_bridge_863(output)
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
