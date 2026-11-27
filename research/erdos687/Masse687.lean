import SurvieTotale687

/-! A version of the survivor bound controlled by the reciprocal sum of
    the actual moduli, with the denominator capped at x. -/
namespace Masse687
open Filter GainVariable687 Transfert687 SurvieTotale687

noncomputable def weight (x : ℕ) (P : Finset ℕ) : ℝ := ∑ p ∈ P, (1:ℝ)/(min p x:ℕ)

/-- No density or cutoff distribution for P is assumed. Small capped
    reciprocal mass guarantees that half the old stock remains. -/
theorem weighted_survival (source : InterfaceSource687.statement) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 →
      ∀ᶠ x : ℕ in atTop, ∀ (a : ℕ → ℕ) (P : Finset ℕ),
        (∀ p ∈ P, p.Prime ∧ ⌊top d x⌋₊ < p) →
        weight x P ≤ (c/70)*(Real.log (Real.log x)/Real.log x) →
        (c/2)*stockUnit d x ≤ ((remaining (survivors ⌊top d x⌋₊ (length d x) a) P a).card:ℝ) := by
  obtain ⟨c,hc,stock⟩ := StockSource687.stock_of_published (StockSource687.source_of_interface source)
  refine ⟨c,hc,?_⟩
  intro d hd hh
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [stock d hd hh,CribleTransfert687.progression_at_reference hd hh,
    logs.eventually_ge_atTop 2] with x hs sieve hL
  intro a P new mass
  let S := survivors ⌊top d x⌋₊ (length d x) a
  let V := classUnit d x
  have nonneg : 0 ≤ V := div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have topx : top d x ≤ (x:ℝ) := div_le_self (Nat.cast_nonneg _)
    (Real.one_le_rpow (by change 2 ≤ Real.log (x:ℝ) at hL; linarith) hd.le)
  have loss : (∑ p ∈ P, (charge S a p:ℝ)) ≤ (c/2)*stockUnit d x := calc
    _ ≤ ∑ p ∈ P, 35*(V/(min p x:ℕ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨prime,large⟩ := new p hp
      have topp : top d x ≤ (p:ℝ) := (Nat.lt_floor_add_one _).le.trans (by
        exact_mod_cast (show ⌊top d x⌋₊+1 ≤ p by omega))
      have ref : top d x ≤ (min p x:ℕ) := by rw [Nat.cast_min]; exact le_min topp topx
      exact sieve a (min p x) p (min_le_right _ _) ref (min_le_left _ _) prime large
    _ = (35*V)*weight x P := by simp only [weight,Finset.mul_sum,mul_one_div,mul_div_assoc]
    _ ≤ (35*V)*((c/70)*(Real.log (Real.log x)/Real.log x)) :=
      mul_le_mul_of_nonneg_left mass (by positivity)
    _ = _ := by dsimp [stockUnit,V]; ring
  have budget : (S.card:ℝ) ≤ (remaining S P a).card + ∑ p ∈ P, (charge S a p:ℝ) := by
    exact_mod_cast finite_loss S P a
  have start : c*stockUnit d x ≤ (S.card:ℝ) := hs a
  change (c/2)*stockUnit d x ≤ ((remaining S P a).card:ℝ)
  linarith

/-- In particular a covering assignment at this height must pay a definite
    reciprocal mass on its primes beyond the lower cutoff. -/
theorem necessary_mass (source : InterfaceSource687.statement) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 →
      ∀ᶠ x : ℕ in atTop, ∀ (a : ℕ → ℕ) (P : Finset ℕ),
        (∀ p ∈ P, p.Prime ∧ ⌊top d x⌋₊ < p) →
        remaining (survivors ⌊top d x⌋₊ (length d x) a) P a = ∅ →
        c*(Real.log (Real.log x)/Real.log x) < weight x P := by
  obtain ⟨c,hc,survive⟩ := weighted_survival source
  refine ⟨c/70,by positivity,?_⟩
  intro d hd hh
  filter_upwards [survive d hd hh,stockUnit_pos hd hh] with x bound pos
  intro a P prime empty
  by_contra! small
  have h := bound a P prime small
  rw [empty,Finset.card_empty,Nat.cast_zero] at h
  exact (not_lt_of_ge h) (mul_pos (by positivity) pos)

end Masse687
