import BorneNative687


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
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
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


/-! An asymptotic upper sieve with leading constant two for arbitrary
residue classes, obtained from the finite interval Selberg inequality. -/
namespace CribleFin687
open Filter OAI.Erdos970.NumberTheoryLean

theorem asymptotic_interval (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ J : ℕ in atTop, ∀ z : ℕ, J ≤ z → ∀ residue : ℕ → ℕ,
      ((LargePrimeDeletion.cutoffSurvivors J z residue).card:ℝ) ≤
        (2+ε)*((J:ℝ)/Real.log J) := by
  let t := (2+ε/2)⁻¹
  have tp : 0 < t := by dsimp [t]; positivity
  have half : t < 1/2 := by dsimp [t]; rw [inv_eq_one_div]; exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  have gap : 0 < 1-2*t := by linarith
  have inf := (tendsto_natCast_atTop_atTop : Tendsto (fun J : ℕ => (J:ℝ)) atTop atTop)
  have slow := (isLittleO_log_rpow_rpow_atTop 3 gap).comp_tendsto inf
  filter_upwards [slow.bound (show 0 < ε/8 by positivity),
    (Real.tendsto_log_atTop.comp inf).eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with J cmp logs hj
  intro z hz residue
  let L := Real.log (J:ℝ)
  let R := ⌊(J:ℝ)^t⌋₊
  have jp : 0 < (J:ℝ) := by exact_mod_cast hj
  have one : (1:ℝ) ≤ J := by exact_mod_cast hj
  have L1 : 1 ≤ L := logs
  have lp : 0 < L := by linarith
  have r1 : 1 ≤ R := (Nat.le_floor_iff (Real.rpow_nonneg jp.le _)).2 (by simpa using Real.one_le_rpow one tp.le)
  have fr : (R:ℝ) ≤ (J:ℝ)^t := Nat.floor_le (Real.rpow_nonneg jp.le _)
  have rj : R ≤ J := by
    exact_mod_cast fr.trans (calc (J:ℝ)^t ≤ (J:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le one (by linarith)
                                  _ = _ := Real.rpow_one _)
  have loglo : t*L ≤ Real.log ((R:ℝ)+1) := by
    have cmp := Real.log_le_log (Real.rpow_pos_of_pos jp t) (Nat.lt_floor_add_one ((J:ℝ)^t)).le
    simpa [Real.log_rpow jp,L] using cmp
  have harm : (harmonic R:ℝ) ≤ 2*L := by
    have hi := harmonic_le_one_add_log R
    have upper := Real.log_le_log (by exact_mod_cast r1 : 0 < (R:ℝ)) (by exact_mod_cast rj : (R:ℝ) ≤ J)
    change _ ≤ 1+Real.log (R:ℝ) at hi
    change Real.log (R:ℝ) ≤ L at upper
    linarith
  have bound := ErreurSelberg687.cutoff_bound J z residue r1 (rj.trans hz)
  have main : (J:ℝ)/Real.log ((R:ℝ)+1) ≤ (2+ε/2)*((J:ℝ)/L) := calc
    _ ≤ (J:ℝ)/(t*L) := div_le_div_of_nonneg_left jp.le (mul_pos tp lp) loglo
    _ = _ := by dsimp [t]; field_simp
  change ‖Real.log (J:ℝ)^(3:ℝ)‖ ≤ (ε/8)*‖(J:ℝ)^(1-2*t)‖ at cmp
  rw [Real.norm_of_nonneg (Real.rpow_nonneg lp.le _),Real.norm_of_nonneg (Real.rpow_nonneg jp.le _)] at cmp
  norm_num only [Real.rpow_ofNat] at cmp
  change L^3 ≤ ε/8*(J:ℝ)^(1-2*t) at cmp
  have pj : ((J:ℝ)^t)^2*(J:ℝ)^(1-2*t) = J := by
    rw [← Real.rpow_mul_natCast jp.le,← Real.rpow_add jp]
    norm_num [show t*(2:ℝ)+(1-2*t)=1 by ring]
  have err : ((R:ℝ)*(harmonic R:ℝ))^2 ≤ (ε/2)*((J:ℝ)/L) := by
    have hn : 0 ≤ (harmonic R:ℝ) := by
      rw [harmonic_eq_sum_Icc,Rat.cast_sum]
      exact Finset.sum_nonneg fun d _ => by simp only [Rat.cast_inv,Rat.cast_natCast]; positivity
    have m := mul_le_mul fr harm hn (Real.rpow_nonneg jp.le _)
    have sq := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hn) m 2
    have cm := mul_le_mul_of_nonneg_left cmp (sq_nonneg ((J:ℝ)^t))
    rw [← mul_div_assoc]
    apply (le_div_iff₀ lp).2
    have scaled := congrArg (fun u : ℝ => (ε/8)*u) pj
    change (ε/8)*(((J:ℝ)^t)^2*(J:ℝ)^(1-2*t)) = (ε/8)*(J:ℝ) at scaled
    nlinarith only [mul_le_mul_of_nonneg_right sq lp.le,cm,scaled]
  change _ ≤ (2+ε)*((J:ℝ)/L)
  linarith only [bound,main,err]

end CribleFin687

#print axioms CribleFin687.asymptotic_interval


/-! A uniform 9/4 progression constant at logarithmic cutoffs. -/
namespace ProgressionFine687
open Filter Transfert687 GainVariable687 Progressions687 CribleTransfert687
open scoped Asymptotics
open OAI.Erdos970.NumberTheoryLean

private theorem length_lower {x : ℕ} {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2)
    (hx : 1 ≤ x) (hL : 4 ≤ Real.log (x:ℝ))
    (hpow : 2*(Real.log (x:ℝ))^4 ≤ (x:ℝ)^(1/100:ℝ)) (hlz : 0 < Real.log (top d x)) :
    (x:ℝ)*(x:ℝ)^(99/100:ℝ) ≤ (length d x : ℝ) := by
  let L := Real.log (x:ℝ)
  have hL' : 4 ≤ L := hL
  have hpos : 0 < L := by linarith
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  have hM : 1 ≤ (x:ℝ)^(99/100:ℝ) := by
    exact Real.one_le_rpow (by exact_mod_cast hx) (by norm_num)
  have hden : L^d ≤ L := by
    simpa using (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (show d ≤ 1 by linarith))
  have hlow : (x:ℝ)/L ≤ top d x :=
    div_le_div_of_nonneg_left hxpos.le (Real.rpow_pos_of_pos hpos _) hden
  have htop : top d x ≤ x := div_le_self hxpos.le (Real.one_le_rpow (by linarith) hd.le)
  have hlog := Real.log_le_log (div_pos hxpos (Real.rpow_pos_of_pos hpos d)) htop
  change Real.log (top d x) ≤ L at hlog
  have big : 2*(x:ℝ)*(x:ℝ)^(99/100:ℝ) ≤ ((x:ℝ)/L)^2 / L^2 := by
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (x:ℝ)*(x:ℝ)^(99/100:ℝ) by positivity)
    have hs : (x:ℝ)^(99/100:ℝ)*(x:ℝ)^(1/100:ℝ) = x := by rw [← Real.rpow_add hxpos]; norm_num
    have hprod : 2*(x:ℝ)*(x:ℝ)^(99/100:ℝ)*L^4 ≤ (x:ℝ)^2 := by
      calc
        _ = ((x:ℝ)*(x:ℝ)^(99/100:ℝ))*(2*L^4) := by ring
        _ ≤ ((x:ℝ)*(x:ℝ)^(99/100:ℝ))*(x:ℝ)^(1/100:ℝ) := hp
        _ = (x:ℝ) * ((x:ℝ)^(99/100:ℝ)*(x:ℝ)^(1/100:ℝ)) := by ring
        _ = (x:ℝ)^2 := by rw [hs]; ring
    calc
      _ ≤ (x:ℝ)^2/L^4 := (le_div_iff₀ (by positivity)).2 hprod
      _ = _ := by field_simp
  have cmp : ((x:ℝ)/L)^2/L^2 ≤ (top d x)^2/(Real.log (top d x))^2 := by gcongr
  have floorlt := Nat.lt_floor_add_one ((top d x)^2/(Real.log (top d x))^2)
  change _ < (length d x : ℝ)+1 at floorlt
  have h1 : (1:ℝ) ≤ (x:ℝ)*(x:ℝ)^(99/100:ℝ) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hx) hM
  linarith [big.trans cmp]

/-- A class modulo q can be estimated using any smaller reference modulus p
    between the real cutoff and x. This includes primes q above x. -/
theorem progression_at_reference {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, ∀ (a : ℕ → ℕ) (p q : ℕ), p ≤ x → top d x ≤ (p:ℝ) →
      p ≤ q → q.Prime → ⌊top d x⌋₊ < q →
      (charge (survivors ⌊top d x⌋₊ (length d x) a) a q : ℝ) ≤ (9/4)*(classUnit d x/p) := by
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have inf := (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  have slow := ((isLittleO_log_rpow_rpow_atTop 4 (by norm_num : 0 < (1/100:ℝ))).comp_tendsto inf).bound
    (by norm_num : 0 < (1/2:ℝ))
  obtain ⟨Jmin,hfilter⟩ := eventually_atTop.mp (CribleFin687.asymptotic_interval (1/10) (by norm_num))
  have grow := (tendsto_rpow_atTop (by norm_num : 0 < (99/100:ℝ))).comp inf
  filter_upwards [hinf.eventually_ge_atTop 4, eventually_ge_atTop (1:ℕ),slow,
    grow.eventually_ge_atTop (max (Jmin:ℝ) 100)] with x hL hx hslow huge
  let L := Real.log (x:ℝ)
  let z := top d x
  let N := length d x
  have hL' : 4 ≤ L := hL
  have hl : 0 < L := by linarith
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  change max (Jmin:ℝ) 100 ≤ (x:ℝ)^(99/100:ℝ) at huge
  change ‖L^(4:ℝ)‖ ≤ (1/2:ℝ)*‖(x:ℝ)^(1/100:ℝ)‖ at hslow
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl.le _), Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] at hslow
  norm_num only [Real.rpow_ofNat] at hslow
  have hpow : 2*L^4 ≤ (x:ℝ)^(1/100:ℝ) := by linarith
  have hpden := Real.rpow_pos_of_pos hl d
  have hlog : Real.log z = L-d*Real.log L := by
    change Real.log ((x:ℝ)/L^d) = _
    rw [Real.log_div hxpos.ne' hpden.ne', Real.log_rpow hl]
  have hlower : L/2 ≤ Real.log z := by
    rw [hlog]
    linarith [mul_le_mul_of_nonneg_right hh (Real.log_nonneg (show 1 ≤ L by linarith)),
      Real.log_le_sub_one_of_pos hl]
  have hzlog : 2 ≤ Real.log z := by linarith
  have hzpos : 0 < z := div_pos hxpos hpden
  have hz : 2 ≤ z := by linarith [Real.log_le_sub_one_of_pos hzpos]
  have hN : (x:ℝ)*(x:ℝ)^(99/100:ℝ) ≤ (N:ℝ) := length_lower hd hh hx hL hpow (by linarith)
  have hNup : (N:ℝ) ≤ z^2 / (Real.log z)^2 := Nat.floor_le (by positivity)
  intro a p q px hzpr hpq prime hzp
  change z ≤ (p:ℝ) at hzpr
  have hpr := hzpos.trans_le hzpr
  have ppos : 0 < p := by exact_mod_cast hpr
  let M := (N:ℝ)/p
  let J := N/p+1
  have hMJ : M ≤ (J:ℝ) := (div_le_iff₀ hpr).2 (by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul ppos).1 (Nat.lt_succ_self (N/p))).le)
  have hJM : (J:ℝ) ≤ M+1 := by
    dsimp [J,M]; push_cast
    exact add_le_add Nat.cast_div_le (le_refl (1:ℝ))
  have hMlow : (x:ℝ)^(99/100:ℝ) ≤ M := (le_div_iff₀ hpr).2 <| calc
    _ ≤ (x:ℝ)^(99/100:ℝ)*(x:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast px) (by positivity)
    _ = _ := mul_comm _ _
    _ ≤ _ := hN
  have hMup : M ≤ z/2 := (div_le_iff₀ hpr).2 <| calc
    (N:ℝ) ≤ z^2/(Real.log z)^2 := hNup
    _ ≤ z^2/(2:ℝ)^2 := by gcongr
    _ ≤ (z/2)*p := by nlinarith [mul_le_mul_of_nonneg_left hzpr hzpos.le, sq_nonneg z]
  have hJz : J ≤ ⌊z⌋₊ := (Nat.le_floor_iff hzpos.le).2 (by linarith)
  have hlogJ : (99/100)*L ≤ Real.log (J:ℝ) := by
    simpa only [Real.log_rpow hxpos] using Real.log_le_log (Real.rpow_pos_of_pos hxpos (99/100)) (hMlow.trans hMJ)
  have hmin : Jmin ≤ J := by exact_mod_cast ((le_max_left _ _).trans (huge.trans (hMlow.trans hMJ)))
  have h100 : (100:ℝ) ≤ M := (le_max_right _ _).trans (huge.trans hMlow)
  have hquot : (J:ℝ)/Real.log J ≤ (15/14)*(M/L) := calc
    _ ≤ ((101/100)*M)/((99/100)*L) := by gcongr; linarith
    _ ≤ _ := by
      have eq : ((101/100)*M)/((99/100)*L) = (101/99)*(M/L) := by ring
      rw [eq]
      exact mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg (by linarith) hl.le)
  obtain ⟨b,hb⟩ := charge_le_index_sieve (N := N) prime hzp a
  have incl : siftedIndices ⌊z⌋₊ (N/q+1) b ⊆ siftedIndices ⌊z⌋₊ J b := by
    intro i hi
    obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hI).trans_le (Nat.add_le_add_right (Nat.div_le_div_left hpq ppos) 1)),avoid⟩
  have embedded := hb.trans (Finset.card_le_card incl)
  rw [index_eq_cutoff] at embedded
  have found := hfilter J hmin ⌊z⌋₊ hJz b
  calc
    _ ≤ ((LargePrimeDeletion.cutoffSurvivors J ⌊z⌋₊ b).card:ℝ) := by exact_mod_cast embedded
    _ ≤ (21/10)*((J:ℝ)/Real.log J) := by convert found using 1 <;> norm_num
    _ ≤ (21/10)*((15/14)*(M/L)) := mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = (9/4)*(M/L) := by ring
    _ = _ := by unfold classUnit; dsimp [M,N,L]; ring

theorem uniform_progression {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    progressionBound (9/4) d := by
  filter_upwards [progression_at_reference hd hh] with x estimate
  intro a p hp
  obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hin
  have large : ⌊top d x⌋₊ < p := lt_of_not_ge fun h => hout (Nat.mem_primesLE.mpr ⟨h,prime⟩)
  have ref : top d x ≤ (p:ℝ) := (Nat.lt_floor_add_one _).le.trans
    (by exact_mod_cast (show ⌊top d x⌋₊+1 ≤ p by omega))
  exact estimate a p p le ref le_rfl prime large

end ProgressionFine687

#print axioms ProgressionFine687.uniform_progression
