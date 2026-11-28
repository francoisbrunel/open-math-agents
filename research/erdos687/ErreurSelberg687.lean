import NormalisationSelberg687

/-! An averaged bound on the absolute Selberg weights for a translated
interval. Summing the incidence d ∣ l before estimating costs only a
harmonic factor in the radius. -/
namespace ErreurSelberg687
open OAI.Erdos970.NumberTheoryLean SelbergOptimization
open scoped BigOperators

private theorem divisor_sum {l R : ℕ} (hl : 0 < l) (hR : l ≤ R) :
    (∑ d ∈ l.divisors, (d:ℝ)) ≤ (R:ℝ)*(harmonic R:ℝ) := by
  have flip := Nat.sum_div_divisors l (fun d : ℕ => (d:ℝ))
  have heq : (∑ d ∈ l.divisors, (d:ℝ)) = ∑ d ∈ l.divisors, (l:ℝ)*(d:ℝ)⁻¹ := by
    rw [← flip]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne' : (d:ℝ) ≠ 0), div_eq_mul_inv]
  have harmonicBound : (∑ d ∈ l.divisors, (d:ℝ)⁻¹) ≤ (harmonic R:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    simp only [Rat.cast_inv,Rat.cast_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact fun d hd => Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,(Nat.le_of_dvd hl (Nat.dvd_of_mem_divisors hd)).trans hR⟩
    · intro d _ _; positivity
  rw [heq,← Finset.mul_sum]
  exact mul_le_mul (by exact_mod_cast hR) harmonicBound (Finset.sum_nonneg fun _ _ => by positivity) (Nat.cast_nonneg _)

private theorem restricted_mass (P d : ℕ) (hP : 0 < P) (hd : d ∣ P) (f : ℕ → ℝ) :
    (∑ t ∈ (P/d).divisors, f (P/t)) = ∑ l ∈ P.divisors, if d ∣ l then f l else 0 := by
  rw [← sum_multiples_reverse P d hP hd (fun t => f (P/t))]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hl) hP.ne']

theorem sum_weights (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R)
    (density : ∀ d, d ∣ s.prodPrimes → s.nu d = (d:ℝ)⁻¹) :
    (∑ d ∈ s.prodPrimes.divisors, |optimizedWeight s R d|) ≤ (R:ℝ)*(harmonic R:ℝ) := by
  classical
  let P := s.prodPrimes
  let f := fun l : ℕ => |diagonalTarget s R l|
  have pp : 0 < P := Nat.pos_of_ne_zero s.prodPrimes_squarefree.ne_zero
  have point (d : ℕ) (hd : d ∈ P.divisors) : |optimizedWeight s R d| ≤
      ∑ l ∈ P.divisors, if d ∣ l then (d:ℝ)*f l else 0 := by
    have dvd := Nat.dvd_of_mem_divisors hd
    have raw := lowerMobius_abs_le (fun t => diagonalTarget s R (P/t)) (P/d)
    change |inverseMultiples P (diagonalTarget s R) d| ≤ ∑ t ∈ (P/d).divisors, f (P/t) at raw
    rw [restricted_mass P d pp dvd f] at raw
    rw [optimizedWeight, abs_div,density d dvd,abs_of_nonneg (show 0 ≤ (d:ℝ)⁻¹ by positivity),div_inv_eq_mul,mul_comm]
    refine (mul_le_mul_of_nonneg_left raw (Nat.cast_nonneg d)).trans_eq ?_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp
  have col (l : ℕ) (hl : l ∈ P.divisors) :
      (∑ d ∈ P.divisors, if d ∣ l then (d:ℝ)*f l else 0) ≤ ((R:ℝ)*(harmonic R:ℝ))*f l := by
    by_cases small : l ≤ R
    · rw [← Finset.sum_filter,Nat.divisors_filter_dvd_of_dvd pp.ne' (Nat.dvd_of_mem_divisors hl),← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (divisor_sum (Nat.pos_of_mem_divisors hl) small) (abs_nonneg _)
    · simp [f,diagonalTarget,small]
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ l ∈ P.divisors, if d ∣ l then (d:ℝ)*f l else 0 := Finset.sum_le_sum point
    _ = ∑ l ∈ P.divisors, ∑ d ∈ P.divisors, if d ∣ l then (d:ℝ)*f l else 0 := Finset.sum_comm
    _ ≤ ∑ l ∈ P.divisors, ((R:ℝ)*(harmonic R:ℝ))*f l := Finset.sum_le_sum col
    _ = _ := by rw [← Finset.mul_sum]; change _*(∑ l ∈ s.prodPrimes.divisors, |diagonalTarget s R l|) = _; rw [sum_abs_diagonalTarget s hR,mul_one]

theorem cutoff_bound (J z : ℕ) (residue : ℕ → ℕ) {R : ℕ} (hR : 1 ≤ R) (cut : R ≤ z) :
    ((LargePrimeDeletion.cutoffSurvivors J z residue).card:ℝ) ≤
      (J:ℝ)/Real.log ((R:ℝ)+1) + ((R:ℝ)*(harmonic R:ℝ))^2 := by
  let s := IntervalBoundingSieve.intervalSieve 0 0 (IntervalBoundingSieve.cutoffProduct z)
    (IntervalBoundingSieve.cutoffProduct_squarefree z)
  let muPlus := BoundingSieve.lambdaSquared (optimizedWeight s R)
  have crude := IntervalBoundingSieve.cutoffSurvivors_card_le_upperMoebius J z residue muPlus
    (optimized_upperMoebius s hR)
  have main : (∑ d ∈ (IntervalBoundingSieve.cutoffProduct z).divisors, muPlus d / d) = (cutoffNormalization z R)⁻¹ := by
    change s.mainSum muPlus = (normalization s R)⁻¹
    exact optimized_mainSum s hR
  have logpos : 0 < Real.log ((R:ℝ)+1) := Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hR)
  have weights := sum_weights s hR (fun _ _ => rfl)
  have err := sum_abs_lambdaSquared_le s.prodPrimes (optimizedWeight s R)
  rw [main,← div_eq_mul_inv] at crude
  exact crude.trans (add_le_add (div_le_div_of_nonneg_left (Nat.cast_nonneg J) logpos
    (NormalisationSelberg687.log_le_normalization cut)) (err.trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) weights 2)))

end ErreurSelberg687

#print axioms ErreurSelberg687.sum_weights
#print axioms ErreurSelberg687.cutoff_bound
