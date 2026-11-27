"""Enumerate two-ended, 28-position extensions of an old maximal cover."""
from collections import Counter
from itertools import product


SMALL = (2, 3, 5, 7)
WIDTH = 28


def survives(n, residues):
    return all(n % p != a for p, a in zip(SMALL, residues))


def profiles():
    residues = list(product(*(range(p) for p in SMALL)))
    best_counts = Counter()
    obstructions = []
    for y in range(1, 210, 2):
        for a in residues:
            if not survives(0, a) or not survives(y + 1, a):
                continue
            left = tuple(-j for j in range(WIDTH) if survives(-j, a))
            right = tuple(j for j in range(1, WIDTH + 1) if survives(y + j, a))
            best = min(
                sum(n > -length for n in left) + sum(j <= WIDTH - length for j in right)
                for length in range(WIDTH + 1)
            )
            best_counts[best] += 1
            if best > 7:
                # Removing a point of either one-sided extension suffices.
                assert len(left) == len(right) == 8
                obstructions.append((y, a, left, right))
    return best_counts, obstructions


def lift(obstructions, primes):
    periods = 1
    for p in primes:
        periods *= p
    failures = set()
    for y, _, left, right in obstructions:
        for k in range(periods):
            length = y + 210 * k
            points = left + tuple(length + j for j in right)
            if all(len({i % p for i in points}) < p for p in primes):
                failures.add(length)
    return failures


if __name__ == "__main__":
    counts, bad = profiles()
    print("Small-prime profiles by their best surviving count:", sorted(counts.items()))
    print("Exceptional lengths modulo 210:", sorted({y for y, *_ in bad}))
    print("Profiles still requiring eight primes:", len(bad))
    for primes in ((11,), (13,), (11, 13)):
        print("Additional old primes", primes, "give", len(lift(bad, primes)),
              "exceptional odd residues in the enlarged period.")
