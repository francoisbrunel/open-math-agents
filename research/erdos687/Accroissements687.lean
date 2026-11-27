import Presque687

/-! The contribution of new primes to a complete cover, in both
    directions. -/
namespace Accroissements687
open Extension687 Progressions687 Transfert687 Presque687
open OAI.Erdos970.NumberTheoryLean

private theorem eighth {J z : ℕ} (cap : J ≤ z^8) : Nat.nthRoot 8 J ≤ z := by
  apply Nat.lt_succ_iff.mp ((Nat.nthRoot_lt_iff (by norm_num : 8 ≠ 0)).mpr ?_)
  exact cap.trans_lt (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by norm_num : 8 ≠ 0))

theorem extreme {J z : ℕ} (big : 256 ≤ J) (cap : J ≤ z^8) (b : ℕ → ℕ) :
    ((siftedIndices z J b).card:ℝ) ≤ 17*J/Real.log J := by
  rw [CribleTransfert687.index_eq_cutoff]
  exact SquarefreeHarmonic.cutoffSurvivors_le_seventeen J z b big (eighth cap)

/-- The old optimal interval can be extended by at least floor(r log r/17)
    whenever r fresh primes are available and r <= z. -/
theorem gain_log {z x r : ℕ} (hzx : z ≤ x) (rz : r ≤ z)
    (fresh : r ≤ (x.primesLE \ z.primesLE).card) :
    Erdos687.Y z + ⌊(r:ℝ)*Real.log r/17⌋₊ ≤ Erdos687.Y x := by
  let J := ⌊(r:ℝ)*Real.log r/17⌋₊
  apply growth_from_capacity (J := J) hzx
  intro b
  by_cases direct : J ≤ r
  · exact (Finset.card_filter_le ..).trans (by simpa using direct.trans fresh)
  have nonzero : r ≠ 0 := by
    rintro rfl
    simp [J] at direct
  have rp : (0:ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero nonzero
  have lr := Real.log_nonneg (show (1:ℝ) ≤ r by exact_mod_cast Nat.pos_of_ne_zero nonzero)
  have jle : (J:ℝ) ≤ (r:ℝ)*Real.log r/17 := Nat.floor_le (by positivity)
  have gr : (r:ℝ) < J := by exact_mod_cast Nat.lt_of_not_ge direct
  have logbig : 17 < Real.log (r:ℝ) := by
    by_contra! h
    nlinarith [mul_le_mul_of_nonneg_left h rp.le]
  have r256 : 256 ≤ r := by
    by_contra! low
    have upper := Real.log_le_log rp (show (r:ℝ) ≤ 256 by exact_mod_cast low.le)
    rw [show (256:ℝ) = 2^8 by norm_num,Real.log_pow] at upper
    norm_num at upper
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have square : J ≤ r^2 := by
    have upper := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos rp) rp.le
    exact_mod_cast (show (J:ℝ) ≤ (r:ℝ)^2 by nlinarith)
  have capacity : J ≤ z^8 := square.trans ((Nat.pow_le_pow_left rz 2).trans
    (Nat.pow_le_pow_right (by omega : 0 < z) (by norm_num : 2 ≤ 8)))
  have lj := Real.log_le_log rp gr.le
  have bound := extreme (by omega : 256 ≤ J) capacity b
  have e : 17*(J:ℝ)/Real.log J ≤ r := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left lj rp.le]
  exact (by exact_mod_cast bound.trans e : (siftedIndices z J b).card ≤ r).trans fresh

/-- A complete cover using primes <= X implies a bound on the minimum
    number of holes remaining when only primes <= x may be used. -/
theorem necessary {x X B H : ℕ} (cap : H ≤ Erdos687.Y X) (len : H ≤ B*x)
    (big : 256 ≤ B+1) (radius : B+1 ≤ x^8) :
    (holes x H:ℝ) ≤ ((X.primesLE \ x.primesLE).card:ℝ)*(17*(B+1:ℕ)/Real.log (B+1:ℕ)) := by
  obtain ⟨a,cov⟩ := optimal_cover X
  have covered (n : ℕ) (hn : n ∈ Finset.Icc 1 H) :
      ∃ p ≤ X, p.Prime ∧ n%p = a p%p := by
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hn
    exact cov n (Finset.mem_Icc.mpr ⟨lo,up.trans cap⟩)
  have sum := OMA.R_Erdos687_erdos_687_variants_iwaniec_R2.survivor_le_sum (z := x) a covered
  change (survivors x H a).card ≤ ∑ p ∈ X.primesLE \ x.primesLE, charge (survivors x H a) a p at sum
  have upper (p : ℕ) (hp : p ∈ X.primesLE \ x.primesLE) :
      (charge (survivors x H a) a p:ℝ) ≤ 17*(B+1:ℕ)/Real.log (B+1:ℕ) := by
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
    have pr := (Nat.mem_primesLE.mp hin).2
    have xp : x < p := by
      by_contra! le
      exact hout (Nat.mem_primesLE.mpr ⟨le,pr⟩)
    obtain ⟨b,chargele⟩ := charge_le_index_sieve (N := H) pr xp a
    have div : H/p < B+1 := (Nat.div_lt_iff_lt_mul pr.pos).mpr
      (by nlinarith [Nat.mul_le_mul_left B xp.le,pr.pos])
    have sub : siftedIndices x (H/p+1) b ⊆ siftedIndices x (B+1) b := by
      intro i hi
      obtain ⟨le,avoid⟩ := Finset.mem_filter.mp hi
      have lim := Finset.mem_range.mp le
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),avoid⟩
    exact (show (charge (survivors x H a) a p:ℝ) ≤ (siftedIndices x (B+1) b).card by
      exact_mod_cast chargele.trans (Finset.card_le_card sub)).trans (extreme big radius b)
  calc
    _ ≤ ∑ p ∈ X.primesLE \ x.primesLE, (charge (survivors x H a) a p:ℝ) := by
      exact_mod_cast (holes_le x H a).trans sum
    _ ≤ _ := (Finset.sum_le_sum upper).trans_eq (by simp [nsmul_eq_mul])

/-- At comparable prime cutoffs, a complete cover forces an extra
    logarithmic saving in the exceptional count at half the cutoff. -/
theorem doubling {B x : ℕ} (big : 255 ≤ B) (bx : B ≤ x)
    (cover : B*x ≤ Erdos687.Y (2*x)) :
    (holes x (B*x):ℝ) ≤ 1088*(B*x:ℝ)/(Real.log (B*x:ℝ)*Real.log B) := by
  have xx : 2 ≤ x := by omega
  have bb : (0:ℝ) < B := by positivity
  have xp : (0:ℝ) < x := by positivity
  have lb := Real.log_pos (show (1:ℝ)<B by exact_mod_cast (show 1<B by omega))
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast (show 1<x by omega))
  have b1 : (B+1:ℕ) ≤ x^8 := by
    have s : x^2 ≤ x^8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith
  have raw := necessary cover (le_refl (B*x)) (by omega) b1
  have card : ((((2*x).primesLE \ x.primesLE).card):ℝ) ≤ 16*x/Real.log x := by
    have sub := Finset.card_le_card (Finset.sdiff_subset (s := (2*x).primesLE) (t := x.primesLE))
    rw [Nat.primesLE_card_eq_primeCounting] at sub
    have cnt := Comptage687.prime_count_eight (x := 2*x) (by omega)
    have l := Real.log_le_log xp (show (x:ℝ) ≤ (2*x:ℕ) by exact_mod_cast (show x ≤ 2*x by omega))
    have pos : 0 ≤ (8:ℝ)*(2*x:ℕ) := by positivity
    calc _ ≤ (Nat.primeCounting (2*x):ℝ) := by exact_mod_cast sub
         _ ≤ _ := cnt
         _ ≤ _ := (div_le_div_of_nonneg_left pos lx l).trans_eq (by push_cast; ring)
  have inc := Real.log_le_log bb (show (B:ℝ) ≤ (B+1:ℕ) by exact_mod_cast Nat.le_succ B)
  have cost : 17*((B+1:ℕ):ℝ)/Real.log (B+1:ℕ) ≤ 34*B/Real.log B := by
    refine (div_le_div_of_nonneg_left (by positivity) lb inc).trans ?_
    apply div_le_div_of_nonneg_right _ lb.le
    push_cast
    linarith [show (1:ℝ) ≤ B by exact_mod_cast (show 1 ≤ B by omega)]
  have ratio := Real.log_le_log bb (show (B:ℝ) ≤ x by exact_mod_cast bx)
  have lh : Real.log (B*x:ℝ) ≤ 2*Real.log x := by rw [Real.log_mul bb.ne' xp.ne']; linarith
  have lhpos : 0 < Real.log (B*x:ℝ) := by rw [Real.log_mul bb.ne' xp.ne']; positivity
  have saved := (div_le_div_iff₀ lx lhpos).mpr
    (show (16*(x:ℝ))*Real.log (B*x:ℝ) ≤ 32*x*Real.log x by
      nlinarith [mul_le_mul_of_nonneg_left lh (show 0 ≤ 16*(x:ℝ) by positivity)])
  calc
    _ ≤ _ := raw
    _ ≤ (32*(x:ℝ)/Real.log (B*x:ℝ))*(34*B/Real.log B) :=
      mul_le_mul (card.trans saved) cost (div_nonneg (by positivity) (lb.le.trans inc)) (by positivity)
    _ = _ := by ring

end Accroissements687
