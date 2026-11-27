"""Expérience finie sur Erdős 687. Python 3, bibliothèque standard."""

import argparse
from dataclasses import dataclass
from functools import cache
from math import gcd, isqrt, prod
from time import monotonic


def primes_up_to(limit):
    return [n for n in range(2, limit + 1)
            if all(n % d for d in range(2, isqrt(n) + 1))]


def residue_masks(length, prime):
    return tuple(sum(1 << i for i in range(r, length, prime))
                 for r in range(min(length, prime)))


def available_pairs(positions, classes):
    groups = [positions & bits for bits in classes]
    return tuple(g for g in groups if g.bit_count() == 2)


def pair_cover(positions, remaining_classes, singleton_allowance=0, deadline=None):
    """Tous les groupes résiduels contiennent au plus deux positions."""
    required = positions.bit_count() - len(remaining_classes) - singleton_allowance
    if required <= 0:
        return True
    choices = [available_pairs(positions, classes) for classes in remaining_classes]
    choices = tuple(sorted((c for c in choices if c), key=len))

    @cache
    def matching(index, used, needed):
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutError("Budget de recherche atteint")
        if not needed:
            return True
        if len(choices) - index < needed:
            return False
        for pair in choices[index]:
            if not pair & used and matching(index + 1, used | pair, needed - 1):
                return True
        return matching(index + 1, used, needed)

    return matching(0, 0, required)


@dataclass
class Stats:
    phases: int = 0
    nodes: int = 0
    rejected_capacity: int = 0
    rejected_matching: int = 0


def odd_cover(limit, length, wheel_cutoff=7, singleton_allowance=0, deadline=None):
    """Test exact avec les premiers impairs <= limit et des positions libres."""
    primes = primes_up_to(limit)[1:]
    wheel_primes = tuple(p for p in primes if p <= wheel_cutoff)
    period = prod(wheel_primes)
    remaining = tuple(residue_masks(length, p) for p in primes if p > wheel_cutoff)
    stats = Stats()

    def solve(survivors, classes_left, free_positions):
        stats.nodes += 1
        if deadline is not None and stats.nodes % 128 == 1 and monotonic() >= deadline:
            raise TimeoutError("Budget de recherche atteint")
        count = survivors.bit_count()
        if count <= len(classes_left) + free_positions:
            return True
        capacities = tuple(max(((survivors & b).bit_count() for b in classes), default=0)
                           for classes in classes_left)
        if sum(capacities) + free_positions < count:
            stats.rejected_capacity += 1
            return False
        if max(capacities) <= 2:
            result = pair_cover(survivors, classes_left, free_positions, deadline)
            stats.rejected_matching += int(not result)
            return result

        # Tester les choix du premier qui offre la plus grande classe.
        index = capacities.index(max(capacities))
        choices = sorted({survivors & b for b in classes_left[index]},
                         key=int.bit_count, reverse=True)
        others = classes_left[:index] + classes_left[index + 1:]
        for choice in choices:
            if choice.bit_count() >= 2 and solve(survivors ^ choice, others, free_positions):
                return True
        # Un premier chargé d'au plus une position peut attendre la fin.
        # On pourra choisir son reste une fois les autres positions couvertes.
        return solve(survivors, others, free_positions + 1)

    # Les décalages modulo le produit réalisent tous les choix du petit crible.
    for shift in range(period):
        stats.phases += 1
        survivors = sum(1 << i for i in range(length) if gcd(i + shift, period) == 1)
        if solve(survivors, remaining, singleton_allowance):
            return True, stats
    return False, stats


def cutoff_for_singletons(limit, length, seconds):
    """Plus petit premier z permettant de réserver les p > z à un entier chacun."""
    primes = primes_up_to(limit)
    if not primes:
        raise ValueError("La borne doit être au moins 2.")
    deadline = monotonic() + seconds
    # Indice 0 : aucun premier autorisé à couvrir plusieurs positions.
    low, high = 0, len(primes)
    if length <= high:
        return 0
    while low < high:
        mid = (low + high) // 2
        if mid == 0:
            low = 1
            continue
        can_cover, _ = odd_cover(primes[mid - 1], length // 2, 7, len(primes) - mid, deadline)
        if can_cover:
            high = mid
        else:
            low = mid + 1
    cutoff = primes[low - 1]
    # Le cas où même le dernier premier ne suffit pas doit aussi être distingué.
    if low == len(primes) and not odd_cover(cutoff, length // 2, 7, 0, deadline)[0]:
        return None
    return cutoff


def exact_value(limit, wheel_cutoff, singleton_allowance=0):
    if limit < 2:
        return singleton_allowance, None
    def covered(length):
        return odd_cover(limit, length, wheel_cutoff, singleton_allowance)
    low, high = 0, 1
    while covered(high)[0]:
        low, high = high, 2 * high
    while high - low > 1:
        mid = (low + high) // 2
        if covered(mid)[0]:
            low = mid
        else:
            high = mid
    # Une classe modulo 2 couvre une parité entière. L'autre se comprime
    # en un intervalle ordinaire car 2 est inversible modulo chaque premier impair.
    return 2 * low + 1, covered(high)[1]


def direct_value(limit):
    """Contrôle indépendant : écarts entre entiers premiers au primoriel."""
    modulus = prod(primes_up_to(limit))
    last, largest = 1, 0
    for n in range(2, modulus + 2):
        if gcd(n, modulus) == 1:
            largest = max(largest, n - last - 1)
            last = n
    return largest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limits", type=int, nargs="*", default=[5, 7, 11, 13, 17, 19, 23, 29, 31, 37])
    parser.add_argument("--wheel", type=int, default=7)
    parser.add_argument("--holes", type=int, default=0,
                        help="nombre maximal de positions laissées libres")
    args = parser.parse_args()
    if args.holes < 0:
        parser.error("--holes doit être positif ou nul")
    for x in args.limits:
        value, stats = exact_value(x, args.wheel, args.holes)
        if args.holes == 0 and 2 <= x <= 17:
            assert value == direct_value(x)
        print(f"x={x:3d}  trous={args.holes}  longueur={value:3d}  premier échec: {stats}", flush=True)
