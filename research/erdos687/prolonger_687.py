"""Extend complete prime covers starting from the Weeks v1.0-paper certificates."""
from argparse import ArgumentParser
import ctypes
from itertools import combinations
import json
from pathlib import Path
from random import Random
import subprocess
from time import monotonic
from zipfile import ZipFile

from recherche_687 import primes_up_to


def published(zip_path):
    with ZipFile(zip_path) as archive:
        rows = json.loads(archive.read("jacobsthal_Oct292026/anc/method5b_lower_bound_certificates.json"))
    seeds = {}
    for row in rows["certificates"]:
        k = row["index"]
        primes = primes_up_to(1300)[1:k]
        start = int(row["coprime_x"])
        residues = [(-start*pow(2, -1, p)-1) % p for p in primes]
        width = row["lower_bound"]//2-1
        assert all(any(t % p == r for p, r in zip(primes, residues)) for t in range(width))
        seeds[k] = primes, residues, width
    return seeds


def multi_cover(primes, residues, holes, free, solver, conflicts=10000, timeout=5):
    """Exactly test multi-point classes with a shared budget for singletons.

    A selected modulus costs one unit; an uncovered position also costs one.
    The inequality is exact by ChoixMultiples687.threshold with k = 0.
    """
    limit = len(free)
    if len(holes) <= limit:
        out = residues.copy()
        for pidx,t in zip(sorted(free),holes):
            out[pidx] = t % primes[pidx]
        return out
    clauses, labels, costs = [], {}, []
    incident = [[] for t in holes]
    count = 0
    def new():
        nonlocal count
        count += 1
        return count
    benefit = 0
    for i in sorted(free):
        p = primes[i]
        cells = {}
        for j,t in enumerate(holes):
            cells.setdefault(t%p,[]).append(j)
        groups = [(r,js) for r,js in cells.items() if len(js)>=2]
        if not groups:
            continue
        benefit += max(len(js)-1 for r,js in groups)
        spent = new()
        costs.append(spent)
        previous = None
        for r,js in groups:
            v = new()
            labels[v] = i,r
            for j in js:
                incident[j].append(v)
            clauses.append([-v,spent])
            reached = new()
            clauses.append([-v,reached])
            if previous is not None:
                clauses.extend(([-previous,reached],[-previous,-v]))
            previous = reached
    if len(holes)-limit > benefit:
        return None
    for row in incident:
        if row:
            missed = new()
            costs.append(missed)
            clauses.append([missed,*row])
        else:
            limit -= 1
    if limit<0:
        return None
    # Unary counter. previous[j-1] is forced whenever at least j inputs
    # were true. Overflow of the budget excludes the assignment.
    previous = []
    for v in costs:
        nxt = [new() for _ in range(min(len(previous)+1,limit))]
        for j,s in enumerate(previous):
            clauses.append([-s,nxt[j]])
        if nxt:
            clauses.append([-v,nxt[0]])
        else:
            clauses.append([-v])
        for j,s in enumerate(previous):
            clause = [-s,-v]
            if j+1<len(nxt):
                clause.append(nxt[j+1])
            clauses.append(clause)
        previous = nxt
    cnf = "p cnf %d %d\n" % (count,len(clauses))
    cnf += "\n".join(" ".join(map(str,c))+" 0" for c in clauses)+"\n"
    try:
        run = subprocess.run([str(solver),"-q","-c",str(conflicts)],input=cnf,
                             capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    if run.returncode not in (0,10,20):
        raise RuntimeError(f"SAT solver exited with status {run.returncode}")
    if run.returncode!=10:
        return None
    yes = {int(t) for line in run.stdout.splitlines() if line.startswith("v ") for t in line.split()[1:]}
    out = residues.copy()
    selected = set()
    for v,(i,r) in labels.items():
        if v in yes:
            assert i not in selected
            selected.add(i)
            out[i]=r
    rest = [t for t in holes if all(t%primes[i]!=out[i] for i in selected)]
    assert len(rest)<=len(free-selected)
    for i,t in zip(sorted(free-selected),rest):
        out[i]=t%primes[i]
    return out


def pack_exact(primes, residues, holes, free, candidates, solver, conflicts):
    """A disjoint group of j holes saves j-1 primes versus singletons."""
    want = len(holes)-len(free)
    if want <= 0:
        return None
    moves, prime_rows, spot_rows, values = [], {}, {}, []
    for mask, i, residue in candidates:
        indices = [j for j in range(len(holes)) if (mask >> j) & 1]
        # Large groups remain admissible as complete moves. Their small
        # subgroups can participate in a disjoint packing with other rows.
        if len(indices) > 5:
            groups = [indices]
            if len(indices) <= 12:
                groups.extend(combinations(indices, 2))
        else:
            groups = [g for length in range(2, len(indices)+1) for g in combinations(indices, length)]
        for group in groups:
            moves.append((i, residue, group))
            key = len(moves)
            prime_rows.setdefault(i, []).append(key)
            for j in group:
                spot_rows.setdefault(j, []).append(key)
            values.extend([key]*(len(group)-1))
        if len(values)*want > 45000:
            return None
    if len(values) < want or len(values)*want > 150000:
        return None
    clauses = []
    count = len(moves)
    def fresh():
        nonlocal count
        count += 1
        return count
    for row in [*prime_rows.values(), *spot_rows.values()]:
        if len(row) <= 7:
            clauses.extend([-a, -b] for a,b in combinations(row, 2))
        else:
            last = None
            for var in row:
                flag = fresh()
                clauses.append([-var, flag])
                if last:
                    clauses.extend(([-last, flag], [-var, -last]))
                last = flag
    # reach[k] asserts that at least k benefit units can be attained.
    reach = {}
    for step, var in enumerate(values, 1):
        nxt = {}
        for k in range(max(1, want-(len(values)-step)), min(step, want)+1):
            z = fresh()
            keep = [reach[k]] if k in reach else []
            clauses.append([-z, *keep, var])
            if k > 1:
                take = [reach[k-1]] if k-1 in reach else []
                clauses.append([-z, *keep, *take])
            nxt[k] = z
        reach = nxt
    clauses.append([reach[want]])
    cnf = "p cnf %d %d\n" % (count, len(clauses))
    cnf += "\n".join(" ".join(map(str,c))+" 0" for c in clauses)+"\n"
    try:
        result = subprocess.run([str(solver), "-q", "-c", str(conflicts)], input=cnf,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=7)
    except subprocess.TimeoutExpired:
        return None
    if result.returncode != 10:
        return None
    yes = {int(v) for l in result.stdout.splitlines() if l.startswith("v ") for v in l.split()[1:]}
    found = residues.copy()
    used, covered = set(), set()
    for key,(i, residue, group) in enumerate(moves, 1):
        if key in yes:
            found[i] = residue
            used.add(i)
            covered.update(group)
    rest = [t for j,t in enumerate(holes) if j not in covered]
    assert len(rest) <= len(free-used)
    for i, t in zip(sorted(free-used), rest):
        found[i] = t % primes[i]
    return found


def fill(primes, residues, width, free, random, solver=None, conflicts=5000):
    uncovered = bytearray([1])*width
    for i, (p, r) in enumerate(zip(primes, residues)):
        if i not in free:
            uncovered[r:width:p] = bytes(len(range(r, width, p)))
    holes = [t for t in range(width) if uncovered[t]]
    alive = (1 << len(holes))-1
    rows = list(free)
    candidates = []
    for i in rows:
        p = primes[i]
        buckets = {}
        for j, t in enumerate(holes):
            r = t % p
            buckets[r] = buckets.get(r, 0) | (1 << j)
        candidates.extend((mask, i, r) for r, mask in buckets.items() if mask.bit_count() > 1)
    def solve(alive, rows):
        left = alive.bit_count()
        if left <= len(rows):
            placed = {}
            for i in rows:
                if not alive:
                    break
                bit = alive & -alive
                placed[i] = holes[bit.bit_length()-1] % primes[i]
                alive ^= bit
            return placed
        best = 1
        moves = []
        for mask, i, r in candidates:
            if i not in rows:
                continue
            cover = mask & alive
            count = cover.bit_count()
            if count >= best and count > 1:
                if count > best:
                    best, moves = count, []
                moves.append((cover, i, r))
        if not moves:
            return None
        cover, i, r = random.choice(moves)
        tail = solve(alive ^ cover, rows - {i})
        if tail is not None:
            tail[i] = r
        return tail
    # Reuse the candidate groups across independent greedy packings.
    for _ in range(3):
        changed = solve(alive, set(rows))
        if changed is not None:
            result = residues.copy()
            for i, r in changed.items():
                result[i] = r
            return result
    if solver:
        return pack_exact(primes, residues, holes, free, candidates, solver, conflicts)
    return None


def extended(primes, residues, width):
    def hit(t):
        return any(t % p == r for p, r in zip(primes, residues))
    assert all(hit(t) for t in range(width))
    left, right = 0, width
    while hit(left-1):
        left -= 1
    while hit(right):
        right += 1
    return [(r-left) % p for p, r in zip(primes, residues)], right-left


def walk_step(library, primes, residues, width, random):
    fn = library.improve_cover
    ptr = ctypes.POINTER(ctypes.c_int)
    fn.argtypes = [ctypes.c_int, ctypes.c_int, ptr, ptr, ctypes.c_int, ctypes.c_int, ctypes.c_uint, ptr]
    fn.restype = ctypes.c_int
    n = len(primes)
    numbers = ctypes.c_int*n
    r = numbers(*residues)
    work = (ctypes.c_int*(4*width+n))()
    fixed = random.choice([2, 4, 6, 10, 16, n//3, n//2])
    budget = random.choice([2000, 6000, 12000])
    remaining = fn(width, n, numbers(*primes), r, fixed, budget, random.getrandbits(32), work)
    return list(r) if remaining == 0 else None


def improve(zip_path, output, seconds, seed, solver=None, conflicts=5000, library=None):
    random = Random(seed)
    seeds = published(zip_path)
    records = json.loads(output.read_text()) if output.exists() else {}
    end = monotonic()+seconds
    banks = {}
    for k, (ps, rs, width) in seeds.items():
        banks[k] = [(rs, width)]
        if str(k) in records:
            rec = records[str(k)]
            # File format stores residues on the usual interval [1,Y].
            odd = [(a*pow(2, -1, p)-1) % p for p, a in zip(ps, rec["residues"][1:])]
            banks[k].append(extended(ps, odd, (rec["Y"]-1)//2))
    attempts = 0
    while monotonic() < end:
        for k, (primes, _, original) in seeds.items():
            bank = banks[k]
            best = max(w for _, w in bank)
            residues, old = random.choice([s for s in bank if s[1] >= best-12])
            add = random.choice([0, 1, 1, 2, 3, 4, 6, 8, 12])
            width = max(old, best-3) + add
            left = random.randint(0, width-old)
            shifted = [(r+left) % p for p, r in zip(primes, residues)]
            n = len(primes)
            span = random.randint(max(8, n//5), n-5)
            nfree = random.randint(5, span)
            free = set(random.sample(range(n-span, n), nfree))
            if library is None:
                found = fill(primes, shifted, width, free, random, solver, conflicts)
            else:
                found = walk_step(library, primes, shifted, width, random)
            attempts += 1
            if found is None:
                continue
            new, width = extended(primes, found, width)
            if width >= best-4 and all(new != r for r, _ in bank):
                bank.append((new, width))
                bank.sort(key=lambda t: t[1], reverse=True)
                del bank[30:]
            if width > best:
                normal = [1, *[2*(r+1) % p for p, r in zip(primes, new)]]
                records[str(k)] = {"x": primes[-1], "Y": 2*width+1, "residues": normal}
                pending = output.with_suffix(".tmp")
                pending.write_text(json.dumps(records, sort_keys=True, indent=2)+"\n")
                pending.replace(output)
                print("index", k, "Y >=", 2*width+1, "published", 2*original+1,
                      "attempt", attempts, flush=True)
    print("Completed", attempts, "attempts", flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--seconds", type=float, default=60)
    parser.add_argument("--seed", type=int, default=687)
    parser.add_argument("--solver", type=Path, help="CaDiCaL binary for residue packings")
    parser.add_argument("--conflicts", type=int, default=5000)
    parser.add_argument("--walk-library", type=Path, help="compiled marche_687.c")
    args = parser.parse_args()
    library = ctypes.CDLL(str(args.walk_library.resolve())) if args.walk_library else None
    improve(args.archive, args.output, args.seconds, args.seed, args.solver, args.conflicts, library)
