import PrefixeConditionnel687
import QueueCarree687
import Mathlib.NumberTheory.Bertrand

/-! A conditional exponential bound for the probability that any
assignment to the large primes completes a square-window prefix. -/
namespace ConcentrationUniforme687
open ConcentrationClasses687 MoyenneConditionnelle687 PrefixeConditionnel687 Filter
open scoped BigOperators
noncomputable section

private theorem product_lower {z : ℕ} (hz : 3 ≤ z) :
    1/(3*Real.log z) ≤ product z.primesLE := by
  have eqn : z.primesLE = (Finset.range (z+1)).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  simpa only [product,eqn,OMA_M3.Qm,one_div] using OMA_M3.main z hz

private theorem mean_lower {w z : ℕ} (hz : 1024 ≤ z) (wz : w ≤ z)
    (small : primorial w ≤ z) (a : Rows) :
    (z:ℝ)^2/(6*Real.log z) ≤
      sample (z.primesLE \ w.primesLE).toList (stock z.primesLE (z^2)) a := by
  let P := z.primesLE
  let R := z.primesLE \ w.primesLE
  have zp : (0:ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have lp : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have rem : P \ R = w.primesLE := by
    ext p; simp only [P,R,Finset.mem_sdiff]
    constructor
    · intro h; by_contra n; exact h.2 ⟨h.1,n⟩
    · intro h; exact ⟨Nat.primesLE_mono wz h,fun k => k.2 h⟩
  have cond := conditional_mean P R Finset.sdiff_subset (fun p hp => (Nat.mem_primesLE.mp hp).2) (z^2) a
  rw [rem] at cond
  rw [Nat.cast_pow] at cond
  have lb := mul_le_mul_of_nonneg_left (product_lower (by omega : 3 ≤ z)) (sq_nonneg (z:ℝ))
  have ls : Real.log z ≤ 2*Real.sqrt z := by
    linarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr zp),Real.log_sqrt zp.le]
  have zlarge : (144:ℝ) ≤ z := by exact_mod_cast (show 144 ≤ z by omega)
  have root : 12 ≤ Real.sqrt (z:ℝ) := (Real.le_sqrt (by norm_num) zp.le).mpr (by convert zlarge using 1 <;> norm_num)
  have lr : 6*Real.log z ≤ z := by
    nlinarith only [ls,mul_le_mul_of_nonneg_right root (Real.sqrt_nonneg _),Real.sq_sqrt zp.le]
  have cost : (primorial w:ℝ) ≤ (z:ℝ)^2/(6*Real.log z) := by
    apply (show (primorial w:ℝ) ≤ z by exact_mod_cast small).trans
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left lr zp.le]
  change (z:ℝ)^2*product P ≤ sample R.toList (stock P (z^2)) a+(primorial w:ℝ) at cond
  change _ ≤ sample R.toList (stock P (z^2)) a
  have ident : (z:ℝ)^2*(1/(3*Real.log z))=2*((z:ℝ)^2/(6*Real.log z)) := by ring
  rw [ident] at lb
  linarith only [lb,cond,cost]

private theorem energy_band {w z : ℕ} (hw : 2 ≤ w) (wz : 2*w ≤ z) (K : ℝ) (kp : 0 < K) :
    let R := (z.primesLE \ w.primesLE).toList
    let c := fun p : ℕ => K*(1/(p:ℝ))
    0 < energy R c ∧ energy R c ≤ K^2*(32/((w:ℝ)*Real.log w)) := by
  let R := z.primesLE \ w.primesLE
  let c := fun p : ℕ => K*(1/(p:ℝ))
  have eq : energy R.toList c = K^2*QueueCarree687.band w z := by
    simp only [energy,Finset.sum_map_toList,QueueCarree687.band,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by dsimp [c]; ring)
  obtain ⟨p,pr,greater,last⟩ := Nat.exists_prime_lt_and_le_two_mul w (by omega)
  have mem : p ∈ R := Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨last.trans wz,pr⟩,
    fun h => (not_le_of_gt greater) (Nat.mem_primesLE.mp h).1⟩
  have pos : 0 < QueueCarree687.band w z := by
    apply Finset.sum_pos' (fun _ _ => by positivity)
    refine ⟨p,mem,?_⟩
    have pp : 0 < (p:ℝ) := by exact_mod_cast pr.pos
    positivity
  change 0 < energy R.toList c ∧ energy R.toList c ≤ _
  rw [eq]
  exact ⟨mul_pos (sq_pos_of_pos kp) pos,mul_le_mul_of_nonneg_left (QueueCarree687.upper hw z) (sq_nonneg _)⟩

theorem uniform (m : ℕ) (hm : 288 ≤ m) :
    ∀ᶠ k : ℕ in atTop, let z := k^m
      ∀ w : ℕ, 2 ≤ w → 2*w ≤ z → primorial w ≤ z → ∀ a : Rows,
        chance (z.primesLE \ w.primesLE).toList z (k^(m+1)) (z^2) a ≤
          Real.exp (-((w:ℝ)*Real.log w)/(2*12^2*68^2*32)) := by
  filter_upwards [square_tail m (by omega),eventually_ge_atTop (1024:ℕ)] with k tail hk
  let z := k^m
  let L := Real.log z
  let K := 68*(z:ℝ)^2/L
  let δ := (z:ℝ)^2/(12*L)
  let c := fun p : ℕ => K*(1/(p:ℝ))
  have kp : 0 < k := by omega
  have mp : 1 ≤ m := by omega
  have hz : 1024 ≤ z := hk.trans (by simpa [z] using Nat.pow_le_pow_right kp mp)
  have zp : (0:ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have lp : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have dp : 0 < δ := by dsimp [δ]; positivity
  have Kp : 0 < K := by dsimp [K]; positivity
  dsimp only
  intro w hw wz small a
  let R := z.primesLE \ w.primesLE
  have necessary : (24/(m:ℝ))*(z:ℝ)^2/L+δ ≤ sample R.toList (stock z.primesLE (z^2)) a := by
    apply le_trans _ (mean_lower hz (by omega) small a)
    have mr : (288:ℝ) ≤ m := by exact_mod_cast hm
    have c' : (24:ℝ)/m ≤ 1/12 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right c' (sq_nonneg (z:ℝ))) lp.le
    have id : (z:ℝ)^2/(6*L)=2*δ := by dsimp [δ]; ring
    change _ ≤ (z:ℝ)^2/(6*L)
    have eqd : (1/12:ℝ)*(z:ℝ)^2/L = δ := by dsimp [δ]; ring
    rw [eqd] at h
    rw [id]; linarith only [h]
  have ens := energy_band hw wz K Kp
  have ep : 0 < energy R.toList c := ens.1
  have bound := tail R.toList a δ (fun p hp => (Nat.mem_primesLE.mp
    (Finset.mem_sdiff.mp (Finset.mem_toList.mp hp)).1).2.pos) dp ep necessary
  apply bound.trans
  apply Real.exp_le_exp.mpr
  have wp : 0 < (w:ℝ)*Real.log w := mul_pos (by exact_mod_cast (show 0 < w by omega))
    (Real.log_pos (by exact_mod_cast (show 1 < w by omega)))
  have lw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have compare : (w:ℝ)*Real.log w/(2*12^2*68^2*32) ≤ δ^2/(2*energy R.toList c) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ ((w:ℝ)*Real.log w/(2*12^2*68^2*32))*(2*(K^2*(32/((w:ℝ)*Real.log w)))) := by
        gcongr
        exact ens.2
      _ = _ := by dsimp only [K,δ]; field_simp [lp.ne',wp.ne',lw.ne'] <;> ring
  change -δ^2/(2*energy R.toList c) ≤ -((w:ℝ)*Real.log w)/(2*12^2*68^2*32)
  simpa only [neg_div] using neg_le_neg compare

/-- No condition on the values of the prescribed small rows. The exponent
is proportional to log(z) log(log(z)) at this choice of w. -/
theorem logarithmic (m : ℕ) (hm : 288 ≤ m) :
    ∀ᶠ k : ℕ in atTop, let z := k^m
      let w := Nat.log 16 z
      ∀ a : Rows, chance (z.primesLE \ w.primesLE).toList z (k^(m+1)) (z^2) a ≤
          Real.exp (-((w:ℝ)*Real.log w)/(2*12^2*68^2*32)) := by
  filter_upwards [uniform m hm,eventually_ge_atTop (1024:ℕ)] with k h hk
  let z := k^m
  let w := Nat.log 16 z
  have kp : 0 < k := by omega
  have mp : 1 ≤ m := by omega
  have hz : 1024 ≤ z := hk.trans (by simpa [z] using Nat.pow_le_pow_right kp mp)
  have wlo : 2 ≤ w := Nat.le_log_of_pow_le (by decide : 1 < 16) (by norm_num; omega : 16^2 ≤ z)
  have powle : 16^w ≤ z := Nat.pow_log_le_self 16 (by omega)
  have double (j : ℕ) : 2*j ≤ 16^j := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [pow_succ]
      have t : 0 < 16^j := pow_pos (by decide) _
      omega
  have cost : primorial w ≤ z := (primorial_le_four_pow w).trans
    ((Nat.pow_le_pow_left (by decide : 4 ≤ 16) w).trans powle)
  exact h w wlo ((double w).trans powle) cost

end
end ConcentrationUniforme687
#print axioms ConcentrationUniforme687.uniform
#print axioms ConcentrationUniforme687.logarithmic
