"""Limite du comptage par groupes de premiers pour Erdős 687.

Dans un groupe B, choisir les restes uniformément et indépendamment couvre
chaque position avec probabilité 1 - produit(1 - 1/p, p dans B). La masse
maximale couverte est donc au moins ce multiple de la masse totale, quels
que soient les poids positifs ou nuls sur les positions. Si la somme de ces
probabilités atteint 1, additionner les capacités maximales des groupes ne
peut plus certifier qu'une position survit.

Pour minimiser la somme avec au plus b premiers par groupe, grouper les
premiers consécutifs dans l'ordre croissant, b par b. Le bilan de recherche
donne la preuve par échange.
"""

from argparse import ArgumentParser
from fractions import Fraction
from itertools import accumulate
from math import expm1, fsum, isqrt, log1p, prod


def primes_through(limit):
    candidates = bytearray([1]) * (limit + 1)
    candidates[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if candidates[p]:
            candidates[p * p::p] = bytes((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if candidates[p]]


def exact_coefficient(primes, block_size):
    return sum((1 - prod(Fraction(p - 1, p) for p in primes[i:i + block_size])
                for i in range(0, len(primes), block_size)), Fraction())


def coefficient(log_products, block_size):
    last = len(log_products) - 1
    return fsum(-expm1(log_products[min(i + block_size, last)] - log_products[i])
                for i in range(0, last, block_size))


def minimum_block(primes):
    """Plus petit b pour lequel l'obstruction moyenne descend sous 1."""
    if not primes:
        return 0
    logs = list(accumulate((log1p(-1 / p) for p in primes), initial=0.0))
    low, high = 0, len(primes)
    while high - low > 1:
        mid = (low + high) // 2
        value = coefficient(logs, mid)
        if abs(value - 1) < 1e-9:
            below = exact_coefficient(primes, mid) < 1
        else:
            below = value < 1
        if below:
            high = mid
        else:
            low = mid
    return high


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("limits", nargs="*", type=int, default=[853, 857, 1000, 10000, 100000, 1000000])
    parser.add_argument("--cutoff", type=int, default=7)
    args = parser.parse_args()
    primes = primes_through(max(args.limits))
    for x in args.limits:
        remaining = [p for p in primes if args.cutoff < p <= x]
        b = minimum_block(remaining)
        print(f"x={x:>8}  premiers={len(remaining):>7}  "
              f"groupe minimal={b:>6}  fraction={b/max(1, len(remaining)):.4%}")
