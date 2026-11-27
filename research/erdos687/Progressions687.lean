import Transfert687

namespace Progressions687

open Filter Transfert687 OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

/-- Indices of a progression start at zero. -/
def siftedIndices (z M : ℕ) (b : ℕ → ℕ) : Finset ℕ :=
  (Finset.range M).filter fun k => ∀ q ∈ z.primesLE, k % q ≠ b q % q

/-- Dividing points of one large-prime class by p embeds its survivors in
    an ordinary sifted interval of at most floor(N/p)+1 indices. -/
theorem charge_le_index_sieve {z N p : ℕ} (hp : p.Prime) (hzp : z < p) (a : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, charge (survivors z N a) a p ≤
      (siftedIndices z (N/p+1) b).card := by
  classical
  let t (q : ℕ) := if h : p.Coprime q then (Nat.chineseRemainder h (a p) (a q)).val else 0
  let b (q : ℕ) := t q / p
  refine ⟨b, Finset.card_le_card_of_injOn (fun n : ℕ => n / p) ?_ ?_⟩
  · intro n hn
    obtain ⟨hs, hr⟩ := Finset.mem_filter.mp hn
    obtain ⟨hI, avoid⟩ := Finset.mem_filter.mp hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (Finset.mem_Icc.mp hI).2)), ?_⟩
    intro q hq hindex
    obtain ⟨hqz, hqprime⟩ := Nat.mem_primesLE.mp hq
    have cop : p.Coprime q := (Nat.coprime_primes hp hqprime).2 (by omega)
    have crt : t q ≡ a p [MOD p] ∧ t q ≡ a q [MOD q] := by
      dsimp only [t]
      rw [dif_pos cop]
      exact (Nat.chineseRemainder cop (a p) (a q)).property
    have hrem : n % p = t q % p := hr.trans crt.1.symm
    have idx : n / p ≡ t q / p [MOD q] := hindex
    have hmod := (idx.mul_left p).add_left (n % p)
    have hsame : n ≡ t q [MOD q] := by
      calc
        n = n % p + p * (n / p) := (Nat.mod_add_div _ _).symm
        _ ≡ n % p + p * (t q / p) [MOD q] := hmod
        _ = t q := by rw [hrem, Nat.mod_add_div]
    exact avoid q hq (hsame.trans crt.2)
  · intro n hn m hm heq
    change n / p = m / p at heq
    obtain ⟨_, hr⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, hs⟩ := Finset.mem_filter.mp hm
    calc
      n = n % p + p * (n / p) := (Nat.mod_add_div _ _).symm
      _ = m % p + p * (m / p) := by rw [hr, hs, heq]
      _ = m := Nat.mod_add_div _ _

/-- A uniform bound on ordinary sifted intervals suffices for the second
    step of R2. There is no dependence between their local residues and a. -/
theorem H2_from_index_sieve
    (upper : ∀ᶠ x : ℕ in atTop, ∀ p ∈ x.primesLE \ (x/2).primesLE, ∀ b,
      (siftedIndices (x/2) (x^2/p+1) b).card ≤ 32 * (x / (x.log2+1))) : H2 := by
  apply H2_from_progression
  filter_upwards [upper] with x hx
  intro a p hp
  obtain ⟨hpx, hsmall⟩ := Finset.mem_sdiff.mp hp
  have prime := (Nat.mem_primesLE.mp hpx).2
  have large : x/2 < p := by
    by_contra! hn
    exact hsmall (Nat.mem_primesLE.mpr ⟨hn,prime⟩)
  obtain ⟨b, hb⟩ := charge_le_index_sieve (N := x^2) prime large a
  exact hb.trans (hx p hp b)

end Progressions687
