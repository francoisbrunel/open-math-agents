/* Local changes of one prime residue, seeded with an existing interval
   cover. All reported witnesses are checked independently in Python. */
#ifdef _WIN32
#define EXPORT __declspec(dllexport)
#else
#define EXPORT
#endif

static unsigned next_random(unsigned *state) {
    unsigned x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    return *state = x;
}

static void remove_hole(int t, int *holes, int *where, int *size) {
    int slot = where[t];
    int last = holes[--*size];
    holes[slot] = last;
    where[last] = slot;
}

EXPORT int improve_cover(int width, int n, const int *primes, int *residue,
        int fixed, int budget, unsigned state, int *work) {
    int *count = work;
    int *weight = count + width;
    int *holes = weight + width;
    int *where = holes + width;
    int *tabu = where + width;
    int size = 0;
    if (!state) state = 1;
    for (int t = 0; t < width; ++t) { count[t] = 0; weight[t] = 1; }
    for (int i = 0; i < n; ++i) {
        tabu[i] = 0;
        for (int t = residue[i]; t < width; t += primes[i]) ++count[t];
    }
    for (int t = 0; t < width; ++t) {
        if (!count[t]) { where[t] = size; holes[size++] = t; }
    }
    for (int step = 0; size && step < budget; ++step) {
        int target = holes[next_random(&state) % size];
        int best = -100000000, choice = -1, ties = 0;
        if (step % 19 == 18)
            for (int k = 0; k < size; ++k)
                if (weight[holes[k]] < 200) ++weight[holes[k]];
        for (int i = fixed; i < n; ++i) {
            int p = primes[i], gain = 0, loss = 0, covered = 0, lost = 0;
            int old = residue[i], r = target % p;
            for (int t = r; t < width; t += p)
                if (!count[t]) { gain += weight[t]; ++covered; }
            for (int t = old; t < width; t += p)
                if (count[t] == 1) { loss += weight[t]; ++lost; }
            int delta = covered-lost;
            if (delta == size) { choice = i; break; }
            if (tabu[i] > step) continue;
            int score = 3*(gain-loss)+2*delta;
            if (score > best) { best = score; choice = i; ties = 1; }
            else if (score == best && next_random(&state) % ++ties == 0) choice = i;
        }
        if (choice < 0) continue;
        int p = primes[choice], old = residue[choice], r = target % p;
        for (int t = old; t < width; t += p) {
            if (!--count[t]) { where[t] = size; holes[size++] = t; }
        }
        for (int t = r; t < width; t += p) {
            if (!count[t]++) remove_hole(t, holes, where, &size);
        }
        residue[choice] = r;
        tabu[choice] = step+2+next_random(&state)%10;
    }
    return size;
}
