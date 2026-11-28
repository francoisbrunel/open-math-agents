import EcartsMultiples687
import CentreCarre687

/-! Fixed uncentered orders can never certify square-scale exclusion. -/
namespace OrdreMoments687
open Filter EcartsMultiples687
open scoped BigOperators

private theorem pi_cap (n : ℕ) : n.primeCounting ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting,Nat.primesLE_eq_filter_Icc_one]
  simpa using Finset.card_le_card (Finset.filter_subset Nat.Prime (Finset.Icc 1 n))

private theorem split_count {u v : ℕ} (h : u ≤ v) :
    ((v.primesLE \ u.primesLE).card:ℝ)+(u.primeCounting:ℝ)=v.primeCounting := by
  rw [← Nat.primesLE_card_eq_primeCounting,← Nat.primesLE_card_eq_primeCounting]
  exact_mod_cast Finset.card_sdiff_add_card_eq_card (Nat.primesLE_mono h)

theorem band_size {z x : ℕ} (hz : 128 ≤ z) (zx : z ≤ x) (hl : 1 ≤ Real.log x)
    (wide : 128*(z:ℝ)*(Real.log x)^2 ≤ x) :
    let P := x.primesLE \ z.primesLE
    1/(8*Real.log x) ≤ harmonic P ∧ z ≤ (P.filter fun p => p ≤ P.card).card := by
  let P := x.primesLE \ z.primesLE
  let B := P.card
  let L := Real.log x
  change 1/(8*L) ≤ harmonic P ∧ _ 
  have lp : 0 < L := by dsimp [L]; linarith
  have zl : 1 ≤ L := hl
  have zr : (128:ℝ) ≤ z := by exact_mod_cast hz
  have xp : 0 < (x:ℝ) := by exact_mod_cast (show 0 < x by omega)
  have square : 128*(z:ℝ)*L^2 ≤ x := wide
  have pi := CentreCarre687.pi_lower (n := x) (by exact_mod_cast (show 128 ≤ x by omega))
  have eqn := split_count zx
  change (B:ℝ)+z.primeCounting=x.primeCounting at eqn
  have pz : (z.primeCounting:ℝ) ≤ z := by exact_mod_cast pi_cap z
  have zm : 8*(z:ℝ)*L ≤ x := by
    nlinarith only [square,mul_nonneg (show 0≤(z:ℝ) by positivity)
      (show 0≤L^2-L by nlinarith [mul_nonneg (sub_nonneg.mpr zl) lp.le]),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) z) lp.le]
  have zlim : (z:ℝ) ≤ x/(8*L) := (le_div_iff₀ (by positivity)).2 (by linarith)
  have bsize : (x:ℝ)/(8*L) ≤ B := by
    change (x:ℝ)/(4*L) ≤ x.primeCounting at pi
    linarith only [pi,eqn,pz,zlim,show (x:ℝ)/(4*L)=2*(x/(8*L)) by ring]
  have harmonic_lower : (B:ℝ)/x ≤ harmonic P := calc
    _ = ∑ _p ∈ P, (1:ℝ)/x := by simp [B,div_eq_mul_inv]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨u,pr⟩ := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
      exact one_div_le_one_div_of_le (by exact_mod_cast pr.pos) (by exact_mod_cast u)
  constructor
  · apply le_trans _ harmonic_lower
    apply (le_div_iff₀ xp).2
    simpa only [div_eq_mul_inv,one_mul,mul_comm (8*L)⁻¹ (x:ℝ)] using bsize
  have bbig : 16*(z:ℝ)*L ≤ B := by
    apply le_trans _ bsize
    apply (le_div_iff₀ (by positivity)).2
    nlinarith only [square]
  have zb : z ≤ B := by exact_mod_cast (zlim.trans bsize)
  have bx : B ≤ x := (Finset.card_le_card (Finset.sdiff_subset (t := z.primesLE))).trans
    (by simpa using pi_cap x)
  have pb := CentreCarre687.pi_lower (n := B) (by exact_mod_cast (show 128 ≤ B by omega))
  have lb : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have cmp : Real.log B ≤ L := Real.log_le_log (by exact_mod_cast (show 0 < B by omega)) (by exact_mod_cast bx)
  have lo : 2*(z:ℝ) ≤ B.primeCounting := by
    apply le_trans _ pb
    apply (le_div_iff₀ (by positivity)).2
    nlinarith only [bbig,mul_le_mul_of_nonneg_left cmp (Nat.cast_nonneg (α := ℝ) z),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) z) lp.le]
  have eqb := split_count zb
  have sub : B.primesLE \ z.primesLE ⊆ P.filter (fun p => p ≤ B) := by
    intro p hp
    obtain ⟨pin,out⟩ := Finset.mem_sdiff.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Nat.primesLE_mono bx pin,out⟩,(Nat.mem_primesLE.mp pin).1⟩
  apply le_trans _ (Finset.card_le_card sub)
  exact_mod_cast (show (z:ℝ) ≤ (B.primesLE \ z.primesLE).card by linarith)

private theorem log_small (j : ℕ) (C : ℝ) (cp : 0<C) :
    ∀ᶠ k : ℕ in atTop, C*(Real.log k)^j ≤ k := by
  have h := ((Real.isLittleO_pow_log_id_atTop (n := j)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)).bound (one_div_pos.mpr cp)
  filter_upwards [h,eventually_ge_atTop (1:ℕ)] with k small hk
  change ‖(Real.log k)^j‖ ≤ (1/C)*‖(k:ℝ)‖ at small
  rw [Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hk)) j),
    Real.norm_of_nonneg (Nat.cast_nonneg k)] at small
  have t := mul_le_mul_of_nonneg_left small cp.le
  rwa [← mul_assoc,mul_one_div,div_self cp.ne',one_mul] at t

theorem fixed_order_fails (m j : ℕ) (hm : 2 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ S : Finset ℕ,
      let P := (k^(m+1)).primesLE \ (k^m).primesLE
      ((S.card-j*P.card:ℕ):ℝ)^(j+1) ≤ (harmonic P)^j*(energy S P j:ℝ) := by
  let c : ℝ := (m:ℝ)+1
  have cp : 0<c := by dsimp [c]; positivity
  have hinf := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)
  filter_upwards [log_small 2 (128*c^2) (by positivity),log_small j ((8*c)^j) (by positivity),
    hinf.eventually_ge_atTop 1,eventually_ge_atTop (128:ℕ)] with k wide lim logbig hk
  intro S
  let z := k^m
  let x := k^(m+1)
  have kz : k ≤ z := by simpa [z] using Nat.pow_le_pow_right (by omega : 0<k) (show 1 ≤ m by omega)
  have zx : z ≤ x := Nat.pow_le_pow_right (by omega) (by omega)
  have logx : Real.log x=c*Real.log k := by simp [x,c,Real.log_pow]
  change (1:ℝ) ≤ Real.log k at logbig
  have cl : 1 ≤ c := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have zl : 1 ≤ Real.log x := by rw [logx]; exact one_le_mul_of_one_le_of_one_le cl logbig
  have bound : 128*(z:ℝ)*(Real.log x)^2 ≤ x := by
    rw [logx]
    change _ ≤ ((k^(m+1):ℕ):ℝ)
    rw [pow_succ k m,Nat.cast_mul]
    change _ ≤ (z:ℝ)*k
    nlinarith only [mul_le_mul_of_nonneg_left wide (Nat.cast_nonneg (α := ℝ) z)]
  obtain ⟨h,R⟩ := band_size (hk.trans kz) zx zl bound
  let P := x.primesLE \ z.primesLE
  have lpos : 0 < 8*Real.log x := by linarith
  have unit : 1 ≤ (harmonic P)*(8*Real.log x) := (div_le_iff₀ lpos).mp h
  have powunit := one_le_pow₀ unit (n := j)
  rw [mul_pow] at powunit
  have rr : (8*Real.log x)^j ≤ ((P.filter (fun p => p ≤ P.card)).card:ℝ) := calc
    _ = (8*c)^j*(Real.log k)^j := by rw [logx,← mul_assoc,mul_pow]
    _ ≤ k := lim
    _ ≤ _ := by exact_mod_cast kz.trans R
  apply order_barrier S P j (fun p hp => (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.pos)
  have hn : 0 ≤ harmonic P := Finset.sum_nonneg (fun _ _ => by positivity)
  exact powunit.trans (mul_le_mul_of_nonneg_left rr (pow_nonneg hn j))

end OrdreMoments687
#print axioms OrdreMoments687.fixed_order_fails
