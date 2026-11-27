import Moments687

/-! A quantitative almost-cover from elementary upper-sieve estimates.
    The two independent losses come from prime survivors and smooth
    composite survivors. -/
namespace Restes687
open Filter LongGapsBetweenPrimes Moments687 Presque687

noncomputable def roughSmooth (H W Z : ℕ) : Finset ℕ := by
  classical
  exact (H.smoothNumbersUpTo (Z+1)).filter (Rough W)

theorem thin_rough {B x W Z : ℕ} (hBW : B ≤ W) (hWZ : W ≤ Z) (hZx : Z ≤ x) :
    (holes x (B*x):ℝ) ≤ ((roughSmooth (B*x) W Z).card+((B*x).primesLE.card:ℝ))*
      Croissance687.density (auxiliaryPrimes W Z) := by
  classical
  let Q := auxiliaryPrimes W Z
  let H := B*x
  let A := roughSmooth H W Z
  let T := A ∪ H.primesLE
  have hQ (p : ℕ) (h : p ∈ Q) := mem_auxiliaryPrimes.mp h
  obtain ⟨a,ha⟩ := Croissance687.thin Q T (fun p h => (hQ p h).1.pos)
  let b := fun p => if p ∈ Q then a p else 0
  have bare := Croissance687.candidates (y := Z+1) (hBW.trans (hWZ.trans hZx)) Q (fun p h => by
    obtain ⟨pr,lo,up⟩ := hQ p h
    exact ⟨pr,by omega,by omega,up.trans hZx⟩) a
  have sub : Transfert687.survivors x H b ⊆ Croissance687.remainder T Q a := by
    intro n hn
    obtain ⟨cand,avoid⟩ := Finset.mem_filter.mp (bare hn)
    refine Finset.mem_filter.mpr ⟨?_,avoid⟩
    rcases Finset.mem_union.mp cand with smooth | prime
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr ⟨smooth,?_⟩
      intro p hp dv
      obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp hp
      have out : p ∉ Q := fun h => (hQ p h).2.1.not_ge le
      exact (Finset.mem_filter.mp hn).2 p (Nat.mem_primesLE.mpr ⟨le.trans (hWZ.trans hZx),pr⟩)
        (by simp [b,out,Nat.mod_eq_zero_of_dvd dv])
    · exact Finset.mem_union_right _ prime
  have nn : 0 ≤ Croissance687.density Q := by
    apply Finset.prod_nonneg
    intro p h
    have lo : (1:ℝ) ≤ p := by exact_mod_cast (hQ p h).1.one_le
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr lo)
  have h := (holes_le x H b).trans (Finset.card_le_card sub)
  refine (show (holes x H:ℝ) ≤ _ by exact_mod_cast h).trans (ha.trans ?_)
  apply mul_le_mul_of_nonneg_right _ nn
  exact_mod_cast Finset.card_union_le A H.primesLE

theorem smooth_total {H W Z : ℕ} (hH : 2 ≤ H) (hW : 4 ≤ W) (hWZ : W ≤ Z)
    (room : Z^2*W^5 ≤ H) (scale : Real.log Z ≤ Real.log H/4) (base : Real.log H ≤ W) :
    ((roughSmooth H W Z).card:ℝ) ≤ 4*((H:ℝ)/Real.log H) +
      160*((H:ℝ)/Real.log W)*(Real.log Z/Real.log H)^2 := by
  classical
  let A := roughSmooth H W Z
  let E := A.filter (fun n => ¬Squarefree n)
  let G := A.filter (fun n => Squarefree n ∧ H.sqrt < n)
  have info (n : ℕ) (h : n ∈ A) :
      0 < n ∧ n ≤ H ∧ Rough W n ∧ ∀ p ∈ n.primeFactors, p ≤ Z := by
    obtain ⟨sm,rough⟩ := Finset.mem_filter.mp h
    obtain ⟨hi,smooth⟩ := Nat.mem_smoothNumbersUpTo.mp sm
    refine ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers smooth),hi,rough,?_⟩
    intro p hp
    obtain ⟨prime,dv,_⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.lt_succ_iff.mp (Nat.mem_smoothNumbers'.mp smooth p prime dv)
  have exc := square_errors (W := W) (H := H) E (fun n h => by
    have e := info n (Finset.mem_filter.mp h).1
    exact ⟨e.1,e.2.1⟩) (fun n h => by
    obtain ⟨hn,notSq⟩ := Finset.mem_filter.mp h
    rw [Nat.squarefree_iff_prime_squarefree] at notSq
    push Not at notSq
    obtain ⟨p,prime,dvd⟩ := notSq
    refine ⟨p,?_,dvd⟩
    by_contra! le
    exact (info n hn).2.2.1 p (Nat.mem_primesLE.mpr ⟨le,prime⟩) ((dvd_mul_right p p).trans dvd))
  have good := rough_smooth_squarefree (W := W) (Z := Z) (H := H) (by omega) (by omega)
    hH room scale G (fun n h => by
      obtain ⟨hn,sq,big⟩ := Finset.mem_filter.mp h
      obtain ⟨pos,up,rough,smooth⟩ := info n hn
      refine ⟨pos,up,sq,rough,smooth,?_⟩
      have hpow : (H:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast (Nat.sqrt_lt'.mp big).le
      have hlog := Real.log_le_log (show (0:ℝ) < H by positivity) hpow
      rw [Real.log_pow] at hlog
      norm_num at hlog
      linarith)
  have incl : A ⊆ (Finset.Icc 1 H.sqrt ∪ E) ∪ G := by
    intro n hn
    by_cases small : n ≤ H.sqrt
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨(info n hn).1,small⟩))
    by_cases sq : Squarefree n
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,sq,by omega⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,sq⟩))
  have cnt := (Finset.card_le_card incl).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have cnt' : (A.card:ℝ) ≤ (H.sqrt:ℝ)+E.card+G.card := by
    simp only [Nat.card_Icc] at cnt
    exact_mod_cast (by omega : A.card ≤ H.sqrt+E.card+G.card)
  have lh := Real.log_pos (show (1:ℝ) < H by exact_mod_cast hH)
  have sqrtle : (H.sqrt:ℝ) ≤ 2*((H:ℝ)/Real.log H) := by
    have sq : (H.sqrt:ℝ)^2 ≤ H := by exact_mod_cast Nat.sqrt_le' H
    have root := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) H)
    have rn := Real.sqrt_nonneg (H:ℝ)
    have rr : (H.sqrt:ℝ) ≤ Real.sqrt H := by nlinarith
    have lb := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (show (0:ℝ) < H by positivity))
    rw [Real.log_sqrt (Nat.cast_nonneg H)] at lb
    rw [← mul_div_assoc]
    apply (le_div_iff₀ lh).mpr
    nlinarith [mul_le_mul_of_nonneg_right rr lh.le,mul_le_mul_of_nonneg_left lb rn]
  have ex : (E.card:ℝ) ≤ 2*((H:ℝ)/Real.log H) := by
    apply exc.trans
    calc
      _ ≤ H*(2/Real.log H) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) lh (by linarith)) (Nat.cast_nonneg H)
      _ = _ := by ring
  linarith

/-- The minimum exceptional fraction, normalized by H/log H, is governed
    by log W/log Z plus log Z/log H. -/
theorem band_estimate {B x W Z : ℕ} (hH : 2 ≤ B*x) (hW : 4 ≤ W)
    (hBW : B ≤ W) (hWZ : W ≤ Z) (hZx : Z ≤ x)
    (room : Z^2*W^5 ≤ B*x) (scale : Real.log Z ≤ Real.log (B*x:ℝ)/4)
    (base : Real.log (B*x:ℝ) ≤ W) :
    (holes x (B*x):ℝ) ≤ (B*x:ℝ)/Real.log (B*x:ℝ) *
      (400*Real.exp 6)*(Real.log W/Real.log Z + Real.log Z/Real.log (B*x:ℝ)) := by
  let H := B*x
  have cast : (H:ℝ) = (B:ℝ)*x := by simp [H]
  rw [← cast] at scale base ⊢
  have lH := Real.log_pos (show (1:ℝ) < H by exact_mod_cast hH)
  have lW : 1 ≤ Real.log (W:ℝ) := by
    have le := Real.log_le_log (by norm_num : (0:ℝ) < 4)
      (show (4:ℝ) ≤ W by exact_mod_cast hW)
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow] at le
    norm_num at le
    linarith [Real.log_two_gt_d9]
  have lZ := Real.log_pos (show (1:ℝ) < Z by exact_mod_cast (show 1 < Z by omega))
  have stock := smooth_total (H := H) hH hW hWZ room scale base
  have primes := Comptage687.prime_count_eight hH
  rw [← Nat.primesLE_card_eq_primeCounting] at primes
  have prod := greedy_product_le (by omega : 2 ≤ W) hWZ
  change Croissance687.density _ ≤ _ at prod
  have dp : 0 ≤ Croissance687.density (auxiliaryPrimes W Z) := by
    apply Finset.prod_nonneg
    intro p hp
    have le : (1:ℝ) ≤ p := by exact_mod_cast (mem_auxiliaryPrimes.mp hp).1.one_le
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr le)
  have cost : ((roughSmooth H W Z).card:ℝ)+H.primesLE.card ≤ 12*((H:ℝ)/Real.log H) +
      160*((H:ℝ)/Real.log W)*(Real.log Z/Real.log H)^2 := by
    have add := add_le_add stock primes
    linarith [show 8*(H:ℝ)/Real.log H = 8*(H/Real.log H) by ring]
  have d : Croissance687.density (auxiliaryPrimes W Z) ≤ 2*Real.exp 6*Real.log W/Real.log Z := by
    refine prod.trans ((div_le_div_iff_of_pos_right lZ).mpr ?_)
    nlinarith [mul_le_mul_of_nonneg_left lW (Real.exp_pos 6).le]
  have comb := (thin_rough hBW hWZ hZx).trans (mul_le_mul cost d dp (by positivity))
  refine comb.trans ?_
  have eq : (12*((H:ℝ)/Real.log H)+160*((H:ℝ)/Real.log W)*(Real.log Z/Real.log H)^2)*
        (2*Real.exp 6*Real.log W/Real.log Z) =
      (H/Real.log H)*Real.exp 6*(24*(Real.log W/Real.log Z)+320*(Real.log Z/Real.log H)) := by
    field_simp [lZ.ne',lH.ne',show Real.log (W:ℝ) ≠ 0 by linarith]; ring
  rw [eq]
  have a : 0 ≤ Real.log W/Real.log Z := by positivity
  have b : 0 ≤ Real.log Z/Real.log H := by positivity
  have c : 0 ≤ (H/Real.log H)*Real.exp 6 := by positivity
  nlinarith [mul_nonneg c a,mul_nonneg c b]

end Restes687
