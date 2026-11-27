"""Longueur maximale d'un intervalle contenant au plus k survivants du crible.

Après fixation des classes des premiers <= z, le théorème chinois ramène les
survivants aux entiers premiers à W = produit(p <= z), à translation près.
Pour leur suite croissante r_i prolongée périodiquement, la valeur cherchée
est max_i(r_(i+k+1) - r_i - 1). Le calcul parcourt une période entière par
segments, y compris les écarts traversant la fin de la période.
"""

from argparse import ArgumentParser
from math import prod
from time import monotonic

import numpy as np

from recherche_687 import primes_up_to


def interval_limits(z, quotas, segment_size=1_000_000, deadline=None):
    primes = primes_up_to(z)
    period = prod(primes)
    phi = prod(p - 1 for p in primes)
    # Une révolution de phi survivants ajoute exactement une période.
    steps = {k: divmod(k + 1, phi) for k in quotas}
    remainders = sorted({rest for _, rest in steps.values()} - {0})
    if not remainders:
        return {k: turns * period - 1 for k, (turns, _) in steps.items()}
    keep = max(remainders)
    prefix = np.empty(0, dtype=np.int64)
    tail = np.empty(0, dtype=np.int64)
    maxima = {r: 0 for r in remainders}
    seen = 0

    def scan(points):
        nonlocal tail
        window = np.concatenate((tail, points))
        for r in remainders:
            if window.size > r:
                maxima[r] = max(maxima[r], int((window[r:] - window[:-r]).max()))
        tail = window[-keep:].copy()

    for start in range(1, period + 1, segment_size):
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutError("Budget atteint avant la fin de la période.")
        length = min(segment_size, period + 1 - start)
        sieve = np.ones(length, dtype=bool)
        for p in primes:
            sieve[(-start) % p::p] = False
        points = np.flatnonzero(sieve).astype(np.int64, copy=False) + start
        seen += points.size
        if prefix.size < keep:
            prefix = np.concatenate((prefix, points[:keep - prefix.size]))
        scan(points)
    assert seen == phi
    scan(period + prefix)
    return {k: turns * period + maxima.get(r, 0) - 1
            for k, (turns, r) in steps.items()}


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("z", type=int)
    parser.add_argument("quotas", nargs="+", type=int)
    parser.add_argument("--seconds", type=int, default=180)
    args = parser.parse_args()
    if args.z < 2 or min(args.quotas) < 0 or args.seconds <= 0:
        parser.error("z >= 2, quotas >= 0, durée > 0")
    limits = interval_limits(args.z, args.quotas, deadline=monotonic() + args.seconds)
    for k, length in limits.items():
        print(f"z={args.z:2}  k={k:2}  longueur={length}")
