import ErreurSelberg687
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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
