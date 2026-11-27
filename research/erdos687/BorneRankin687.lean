import RankinSource687
import Fenetres687
import Croissance687

/-! Use the first, bounded-prime stage of the published long-gap proof.
    A subinterval with few survivors can be completed within the cutoff x. -/
namespace BorneRankin687
open Filter LongGapsBetweenPrimes
open scoped Asymptotics

noncomputable def lowerScale (x : ℝ) : ℝ :=
  x*Real.log x*Real.log (Real.log (Real.log x))/Real.log (Real.log x)^2

private theorem scaling : ∀ᶠ v : ℝ in atTop, coverScale v / 262144 ≤ coverScale (v/512) := by
  have t := (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).atTop_div_const
    (show (0:ℝ) < 8 by norm_num)
  have t' := (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).atTop_div_const
    (show (0:ℝ) < 64 by norm_num)
  filter_upwards [eventually_coverScale_div_eight,t.eventually eventually_coverScale_div_eight,
    t'.eventually eventually_coverScale_div_eight] with v h h' h''
  change coverScale (v/8)/64 ≤ coverScale (v/8/8) at h'
  change coverScale (v/64)/64 ≤ coverScale (v/64/8) at h''
  rw [show v/8/8 = v/64 by ring] at h'
  rw [show v/64/8 = v/512 by ring] at h''
  linarith

/-- Classical Rankin-scale lower bound for the exact catalog definition of Y. -/
theorem rankin_lower :
    (fun x : ℕ => lowerScale x) =O[atTop] (fun x : ℕ => (Erdos687.Y x:ℝ)) := by
  have hinf : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have small := hinf.atTop_div_const (show (0:ℝ) < 512 by norm_num)
  apply Asymptotics.IsBigO.of_bound (262144*5/coverEta)
  filter_upwards [small.eventually eventually_covering_residues,hinf.eventually scaling,
    small.eventually_ge_atTop 256,hinf.eventually eventually_cover_parameters] with x source scale hx params
  let u := (x:ℝ)/512
  let z := ⌊u⌋₊
  let H := coverLength coverEta u
  let q := ⌈Real.log x⌉₊
  let Y := Erdos687.Y x
  have ularge : 256 ≤ u := hx
  have uz := Nat.lt_floor_add_one u
  change u < (z:ℝ)+1 at uz
  have zlarge : 128 ≤ z := (Nat.le_floor_iff (by linarith : 0 ≤ u)).mpr
    (by norm_num; linarith)
  have zx : 128*z ≤ x := by
    have hz : (z:ℝ) ≤ u := Nat.floor_le (by linarith)
    have en : (128:ℝ)*z ≤ x := by dsimp [u] at hz; linarith
    exact_mod_cast en
  have xlarge : 2 ≤ x := by omega
  have lz := Real.log_pos (by exact_mod_cast (show 1 < z by omega) : (1:ℝ) < z)
  have lx : 2 ≤ Real.log (x:ℝ) := params.2.1
  have logmono := Real.log_le_log (show (0:ℝ) < z by positivity)
    (show (z:ℝ) ≤ x by exact_mod_cast (show z ≤ x by omega))
  obtain ⟨a,reduced,near⟩ := source
  have agree : Transfert687.survivors z H a =
      LongGapsBetweenPrimes.survivors (Finset.Icc 1 H) z.primesLE a := by
    ext n
    simp only [Transfert687.survivors,LongGapsBetweenPrimes.survivors,Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    apply forall_congr'
    intro p
    apply forall_congr'
    intro hp
    rw [Nat.mod_eq_of_lt (reduced p hp)]
  let r := (x.primesLE \ z.primesLE).card
  have sub : (128*z).primesLE \ z.primesLE ⊆ x.primesLE \ z.primesLE := by
    intro p hp
    obtain ⟨hin,out⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hin
    exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨le.trans zx,prime⟩,out⟩
  have supply : 8*(z:ℝ)/Real.log z ≤ r :=
    (Croissance687.prime_supply zlarge).trans (by exact_mod_cast Finset.card_le_card sub)
  have enough := (div_le_iff₀ lz).mp supply
  have qlarge : Real.log (x:ℝ) ≤ q := Nat.le_ceil _
  have m : ((Transfert687.survivors z H a).card:ℝ) ≤ z := by
    rw [agree]
    change _ ≤ sieveDelta*u at near
    have h := mul_le_mul_of_nonneg_right sieveDelta_lt_half.le (show 0 ≤ u by linarith)
    have zz : (128:ℝ) ≤ z := by exact_mod_cast zlarge
    linarith
  have few : (Transfert687.survivors z H a).card < q*(r+1) := by
    have extra := mul_le_mul_of_nonneg_left (logmono.trans qlarge) (Nat.cast_nonneg (α := ℝ) r)
    have qq : (0:ℝ) < q := by linarith
    have result : ((Transfert687.survivors z H a).card:ℝ) < q*((r:ℝ)+1) := by nlinarith
    exact_mod_cast result
  have length := Fenetres687.length_lt (show z ≤ x by omega) a few
  have length' : (H:ℝ) ≤ q*((Y:ℝ)+1) := by exact_mod_cast length.le
  have hfloor : coverEta*coverScale u < (H:ℝ)+1 := by
    simpa [H,coverLength_eq] using Nat.lt_floor_add_one (coverEta*coverScale u)
  have one : 1 ≤ Y := by
    apply Transfert687.le_Y_of_covered
    refine ⟨fun _ => 1,?_⟩
    intro n hn
    have e : n = 1 := by have h := Finset.mem_Icc.mp hn; omega
    exact ⟨2,xlarge,Nat.prime_two,by rw [e]⟩
  have hy : (1:ℝ) ≤ Y := by exact_mod_cast one
  have ceil := Nat.ceil_lt_add_one (show 0 ≤ Real.log (x:ℝ) by linarith)
  change (q:ℝ) < _ at ceil
  have len : q*((Y:ℝ)+1) ≤ (2*Real.log x)*(2*Y) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have gain := mul_le_mul_of_nonneg_left scale coverEta_pos.le
  change coverEta*(coverScale x/262144) ≤ coverEta*coverScale u at gain
  have cross : coverEta*coverScale x/262144 ≤ 5*(Y:ℝ)*Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_right hy (show 0 ≤ Real.log (x:ℝ) by linarith)]
  have identity : coverScale x = lowerScale x*Real.log x := by unfold coverScale lowerScale; ring
  rw [identity] at cross
  have comp : lowerScale x ≤ (262144*5/coverEta)*Y := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ coverEta_pos).mpr
    apply (le_of_mul_le_mul_right · (by linarith : 0 < Real.log (x:ℝ)))
    nlinarith only [cross]
  have nonneg : 0 ≤ lowerScale x := by
    obtain ⟨_,_,_,hLLL,_⟩ := params
    unfold lowerScale
    positivity
  change ‖lowerScale x‖ ≤ (262144*5/coverEta)*‖(Y:ℝ)‖
  simpa only [Real.norm_eq_abs,abs_of_nonneg nonneg,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) Y)] using comp

end BorneRankin687
