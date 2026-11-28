import CribleOAI687

/-! A lower bound for the interval Selberg normalisation from the exact
Euler factors of the integers with a prescribed set of prime divisors. -/
namespace NormalisationSelberg687
open scoped BigOperators
open OAI.Erdos970.NumberTheoryLean

private theorem local_factor (p : ℕ) (hp : p.Prime) (E : Finset ℕ) :
    (∑ e ∈ E, ((p:ℝ)⁻¹)^(e+1)) ≤ 1/((p:ℝ)-1) := by
  have one : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have pp : 0 < (p:ℝ) := by linarith
  have low : 0 ≤ (p:ℝ)⁻¹ := by positivity
  have high : (p:ℝ)⁻¹ < 1 := (inv_lt_one₀ pp).2 one
  have hs := hasSum_geometric_of_lt_one low high
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  calc
    _ ≤ (1-(p:ℝ)⁻¹)⁻¹*(p:ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (hs.summable.sum_le_tsum E (fun _ _ => by positivity) |>.trans_eq hs.tsum_eq) low
    _ = _ := by field_simp

theorem reciprocal_fibre (S P : Finset ℕ)
    (positive : ∀ n ∈ S, n ≠ 0) (support : ∀ n ∈ S, n.primeFactors = P)
    (primes : ∀ p ∈ P, p.Prime) :
    (∑ n ∈ S, (n:ℝ)⁻¹) ≤ ∏ p ∈ P, 1/((p:ℝ)-1) := by
  classical
  let E := fun p : ℕ => S.image fun n => n.factorization p-1
  let row := fun (n p : ℕ) (_ : p ∈ P) => n.factorization p-1
  let weight := fun (v : (p : ℕ) → p ∈ P → ℕ) =>
    ∏ p ∈ P.attach, ((p.val:ℝ)⁻¹)^(v p.val p.property+1)
  have good (n : ℕ) (hn : n ∈ S) : row n ∈ P.pi E := by
    exact Finset.mem_pi.mpr fun p _ => Finset.mem_image.mpr ⟨n,hn,rfl⟩
  have value (n : ℕ) (hn : n ∈ S) : weight (row n) = (n:ℝ)⁻¹ := by
    have powers : ∀ p ∈ P, n.factorization p - 1 + 1 = n.factorization p := by
      intro p hp
      rw [← support n hn] at hp
      have pos : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
      omega
    have eq : (∏ p ∈ P, p^(n.factorization p))=n := by
      rw [← support n hn]
      exact Nat.prod_factorization_pow_eq_self (positive n hn)
    calc
      _ = ∏ p ∈ P.attach, ((p.val:ℝ)⁻¹)^(n.factorization p.val) := by
        apply Finset.prod_congr rfl
        intro p _
        exact congrArg (fun e : ℕ => ((p.val:ℝ)⁻¹)^e) (powers p p.property)
      _ = ∏ p ∈ P, ((p:ℝ)⁻¹)^(n.factorization p) := Finset.prod_attach P (fun p : ℕ => ((p:ℝ)⁻¹)^(n.factorization p))
      _ = (n:ℝ)⁻¹ := by simp only [inv_pow,Finset.prod_inv_distrib]; exact congrArg Inv.inv (by exact_mod_cast eq : (∏ p ∈ P, (p:ℝ)^(n.factorization p)) = n)
  have inj : Set.InjOn row (S: Set ℕ) := by
    intro n hn m hm eq
    have eqw := congrArg weight eq
    rw [value n hn,value m hm] at eqw
    exact_mod_cast inv_injective eqw
  calc
    _ = ∑ n ∈ S, weight (row n) := Finset.sum_congr rfl fun n hn => (value n hn).symm
    _ = ∑ v ∈ S.image row, weight v := (Finset.sum_image inj).symm
    _ ≤ ∑ v ∈ P.pi E, weight v := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro v hv; obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hv; exact good n hn)
      (by intro v _ _; dsimp [weight]; positivity)
    _ = ∏ p ∈ P, ∑ e ∈ E p, ((p:ℝ)⁻¹)^(e+1) :=
      (Finset.prod_sum P E (fun p e => ((p:ℝ)⁻¹)^(e+1))).symm
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      (fun p hp => local_factor p (primes p hp) _)

private theorem interval_term (z d : ℕ) (sf : Squarefree d) :
    (IntervalBoundingSieve.intervalSieve 0 0 (IntervalBoundingSieve.cutoffProduct z)
      (IntervalBoundingSieve.cutoffProduct_squarefree z)).selbergTerms d =
      ∏ p ∈ d.primeFactors, 1/((p:ℝ)-1) := by
  rw [BoundingSieve.selbergTerms_apply]
  change (d:ℝ)⁻¹*(∏ p ∈ d.primeFactors, (1-(p:ℝ)⁻¹)⁻¹) = _
  have hp : (∏ p ∈ d.primeFactors, (p:ℝ)) = (d:ℝ) := by
    simpa only [Nat.cast_prod] using congrArg (fun t : ℕ => (t:ℝ)) (Nat.prod_primeFactors_of_squarefree sf)
  nth_rw 1 [← hp]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have pp : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  field_simp

/-- The full local Selberg factors give the harmonic number with coefficient one. -/
theorem harmonic_le_normalization {R z : ℕ} (cut : R ≤ z) :
    (harmonic R:ℝ) ≤ SelbergOptimization.cutoffNormalization z R := by
  classical
  let I := Finset.Icc 1 R
  let M := IntervalBoundingSieve.cutoffProduct z
  let D := M.divisors.filter fun d => d ≤ R
  let sieve := IntervalBoundingSieve.intervalSieve 0 0 M (IntervalBoundingSieve.cutoffProduct_squarefree z)
  let rad := fun n : ℕ => ∏ p ∈ n.primeFactors, p
  have maps : ∀ n ∈ I, rad n ∈ D := by
    intro n hn
    obtain ⟨low,hi⟩ := Finset.mem_Icc.mp hn
    have sub : n.primeFactors ⊆ LargePrimeDeletion.cutoffPrimes z := by
      intro p hp
      obtain ⟨pr,dvd,_⟩ := Nat.mem_primeFactors.mp hp
      exact LargePrimeDeletion.mem_cutoffPrimes.mpr ⟨pr,(Nat.le_of_dvd low dvd).trans (hi.trans cut)⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ id sub,
      (IntervalBoundingSieve.cutoffProduct_squarefree z).ne_zero⟩,
      (Nat.le_of_dvd low (Nat.prod_primeFactors_dvd n)).trans hi⟩
  calc
    (harmonic R:ℝ) = ∑ n ∈ I, (n:ℝ)⁻¹ := by
      simp only [I,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ = ∑ d ∈ D, ∑ n ∈ I with rad n=d, (n:ℝ)⁻¹ := (Finset.sum_fiberwise_of_maps_to maps _).symm
    _ ≤ ∑ d ∈ D, sieve.selbergTerms d := by
      apply Finset.sum_le_sum
      intro d hd
      have sf := Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
        (IntervalBoundingSieve.cutoffProduct_squarefree z)
      rw [show sieve.selbergTerms d = _ from interval_term z d sf]
      apply reciprocal_fibre
      · intro n hn
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
        omega
      · intro n hn
        rw [← (Finset.mem_filter.mp hn).2]
        exact (Nat.primeFactors_prod_primeFactors n).symm
      · exact fun _ hp => Nat.prime_of_mem_primeFactors hp
    _ = _ := Finset.sum_filter _ _

theorem log_le_normalization {R z : ℕ} (cut : R ≤ z) :
    Real.log ((R:ℝ)+1) ≤ SelbergOptimization.cutoffNormalization z R := by
  have h := log_add_one_le_harmonic R
  push_cast at h
  exact h.trans (harmonic_le_normalization cut)

end NormalisationSelberg687

#print axioms NormalisationSelberg687.reciprocal_fibre
#print axioms NormalisationSelberg687.log_le_normalization
