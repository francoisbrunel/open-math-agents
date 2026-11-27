"""Vérification indépendante du cas fini de 73 dans le bilan d'Erdős 687."""

from math import gcd, prod


PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73)


def uncovered(length, residues):
    return [n for n in range(1, length + 1)
            if all(n % p != a for p, a in zip(PRIMES, residues))]


def options(classes):
    """Tous les sous-ensembles d'au moins deux points dans une classe."""
    groups = []
    for points in classes:
        subset = points
        while subset:
            gain = subset.bit_count() - 1
            if gain > 0:
                groups.append((gain, subset))
            subset = (subset - 1) & points
    return sorted(groups, reverse=True)


def can_pack(colors, needed):
    """Choisir au plus un groupe par premier, avec des groupes disjoints."""
    choices = sorted((options(rows) for _, rows in colors), key=lambda g: (-g[0][0], len(g)))
    remaining = [0] * (len(choices) + 1)
    for j in reversed(range(len(choices))):
        remaining[j] = remaining[j + 1] + choices[j][0][0]

    def visit(j, used, need):
        if need <= 0:
            return True
        if remaining[j] < need:
            return False
        for gain, group in choices[j]:
            if gain + remaining[j + 1] < need:
                break
            if not (used & group) and visit(j + 1, used | group, need - gain):
                return True
        return visit(j + 1, used, need)

    return visit(0, 0, needed)


def verify_184():
    # Toute parité choisie laisse exactement 92 indices consécutifs, après
    # division du pas par 2. Les classes impaires restent arbitraires.
    length = 92
    wheel = PRIMES[1:6]
    tail = PRIMES[6:-1]
    period = prod(wheel)
    coprime = [gcd(i, period) == 1 for i in range(period)]
    initial = sum(1 << i for i in range(length) if coprime[i])
    residues = [[sum(1 << i for i in range(a, length, p)) for a in range(p)] for p in tail]
    searched = 0
    for shift in range(period):
        # Une position par premier et une position gratuite. Chaque groupe
        # de taille m attribué à un premier économise m-1 positions.
        needed = initial.bit_count() - len(tail) - 1
        colors = []
        for classes in residues:
            hits = [mask & initial for mask in classes]
            rows = [hit for hit in hits if hit.bit_count() >= 2]
            if rows:
                colors.append((max(row.bit_count() - 1 for row in rows), rows))
        if sum(gain for gain, _ in colors) >= needed:
            searched += 1
            if can_pack(colors, needed):
                raise AssertionError(f"Couverture de 184 trouvée à la phase {shift}")
        following = int(coprime[(shift + length) % period])
        initial = (initial >> 1) | (following << (length - 1))
    return period, searched


if __name__ == "__main__":
    witness_183 = (1, 2, 2, 3, 1, 5, 3, 8, 7, 2, 2, 16, 38, 28, 36, 48, 6, 58, 4, 40)
    witness_189 = (1, 2, 1, 4, 6, 12, 14, 2, 1, 25, 21, 26, 1, 22, 37, 5, 30, 10, 51, 49, 34)
    assert uncovered(183, witness_183) == [106]
    assert uncovered(189, witness_189[:-1]) == [34, 180]
    assert uncovered(189, witness_189) == []
    phases, searched = verify_184()
    print(f"{phases} phases vérifiées, dont {searched} nécessitant une recherche de groupes.")
    print("Un seul trou avec les premiers jusqu'à 71 : 183 possible, 184 impossible.")
    print("Témoin de longueur 189 : 34 et 180 sont les seuls entiers couverts uniquement par 73.")
