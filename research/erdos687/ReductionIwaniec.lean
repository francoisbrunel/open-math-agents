import FormalConjectures.ErdosProblems.«687»

-- Reduction of the classical upper bound. Each step concerns the same
-- finite interval and arbitrary prescribed residue classes.
namespace OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

open Filter
open scoped BigOperators

-- A lower sieve through x/2. The slowly growing log-log surplus in the
-- quantitative survivor theorem allows any fixed multiple here eventually.
def H1 : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ a : ℕ → ℕ,
    let small := (x / 2).primesLE
    let S := (Finset.Icc 1 (x^2)).filter fun n => ∀ p ∈ small, n % p ≠ a p % p
    1000 * (x / (x.log2 + 1))^2 < S.card

-- The summed progression upper sieve over the complementary half-band.
def H2 : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ a : ℕ → ℕ,
    let small := (x / 2).primesLE
    let S := (Finset.Icc 1 (x^2)).filter fun n => ∀ p ∈ small, n % p ≠ a p % p
    (∑ p ∈ x.primesLE \ small, (S.filter fun n => n % p = a p % p).card)
      ≤ 1000 * (x / (x.log2 + 1))^2

-- A finite statement valid for any interval length and any cutoff z.
theorem survivor_le_sum {x z N : ℕ} (a : ℕ → ℕ)
    (covered : ∀ n ∈ Finset.Icc 1 N, ∃ p ≤ x, Nat.Prime p ∧ n % p = a p % p) :
    let small := z.primesLE
    let S := (Finset.Icc 1 N).filter fun n => ∀ p ∈ small, n % p ≠ a p % p
    S.card ≤ ∑ p ∈ x.primesLE \ small, (S.filter fun n => n % p = a p % p).card := by
  intro small S
  let band := x.primesLE \ small
  let hits := fun p : ℕ => S.filter fun n => n % p = a p % p
  have incl : S ⊆ band.biUnion hits := by
    intro n hn
    obtain ⟨hI, hs⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, hpx, hp, hres⟩ := covered n hI
    have hsmall : p ∉ small := fun h => hs p h hres
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_sdiff.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hpx, hp⟩, hsmall⟩, Finset.mem_filter.mpr ⟨hn, hres⟩⟩
  exact (Finset.card_le_card incl).trans Finset.card_biUnion_le

-- Also usable at the shorter logarithmic scales of the quantitative sieve.
theorem upper_of_survivor_budget {x z N : ℕ}
    (budget : ∀ a : ℕ → ℕ,
      let S := (Finset.Icc 1 N).filter fun n => ∀ p ∈ z.primesLE, n % p ≠ a p % p
      (∑ p ∈ x.primesLE \ z.primesLE, (S.filter fun n => n % p = a p % p).card) < S.card) :
    Erdos687.Y x ≤ N := by
  apply csSup_le
  · exact ⟨0, fun _ => 0, by simp⟩
  · intro y hy
    obtain ⟨a, ha⟩ := hy
    by_contra! hNy
    have hcov : ∀ n ∈ Finset.Icc 1 N, ∃ p ≤ x, Nat.Prime p ∧ n % p = a p % p := by
      intro n hn
      exact ha n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
        (Finset.mem_Icc.mp hn).2.trans hNy.le⟩)
    exact (Nat.not_lt_of_ge (survivor_le_sum (z := z) a hcov)) (budget a)

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.variants.iwaniec := by
  intro h1 h2
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [h1, h2] with x hstock hloss
  have hbound : Erdos687.Y x ≤ x^2 := upper_of_survivor_budget
    (z := x/2) (fun a => lt_of_le_of_lt (hloss a) (hstock a))
  simpa using (show (Erdos687.Y x : ℝ) ≤ (x : ℝ)^2 by exact_mod_cast hbound)

end OMA.R_Erdos687_erdos_687_variants_iwaniec_R2
