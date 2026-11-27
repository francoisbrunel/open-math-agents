import Troncature687

/-! A single explicit weak cutoff saves every fixed power of the
    logarithm of the least full cutoff. -/
namespace SousExponentiel687
open Filter Inverse687
open scoped Asymptotics

noncomputable def limit (y : ℕ) : ℕ := ⌊(y:ℝ)/Real.exp (Real.sqrt (Real.log y))⌋₊

private theorem logs : Tendsto (fun y : ℕ => Real.log (y:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem roots : Tendsto (fun y : ℕ => Real.sqrt (Real.log y)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp logs

theorem below (y : ℕ) : limit y ≤ y := by
  exact Nat.floor_le_of_le (div_le_self (Nat.cast_nonneg _) (Real.one_le_exp (Real.sqrt_nonneg _)))

private theorem sandwich : ∀ᶠ y : ℕ in atTop, 1 ≤ limit y ∧
    Real.log y-Real.log (limit y) ≤ Real.sqrt (Real.log y)+Real.log 2 ∧
    Real.log (y:ℝ) ≤ 2*Real.log (limit y) := by
  filter_upwards [roots.eventually_ge_atTop 5,eventually_ge_atTop (2:ℕ)] with y root hy
  let L := Real.log (y:ℝ)
  let R := Real.sqrt L
  let V := (y:ℝ)/Real.exp R
  have yp : (0:ℝ)<y := by positivity
  have lp : 0<L := Real.log_pos (show (1:ℝ)<y by exact_mod_cast hy)
  have sq : R^2=L := Real.sq_sqrt lp.le
  change 5 ≤ R at root
  have vp : 0<V := div_pos yp (Real.exp_pos _)
  have lv : Real.log V = L-R := by dsimp only [V,L]; rw [Real.log_div yp.ne' (Real.exp_pos _).ne',Real.log_exp]
  have l2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have v2 : (2:ℝ) ≤ V := (Real.log_le_log_iff (by norm_num) vp).mp (by
    rw [lv]; nlinarith [mul_nonneg (by linarith : 0 ≤ R-5) (by linarith : 0 ≤ R+4)])
  have k : 1 ≤ limit y := (Nat.le_floor_iff vp.le).mpr (by simpa only [Nat.cast_one] using (show (1:ℝ) ≤ V by linarith))
  have kp : (0:ℝ)<limit y := by exact_mod_cast k
  have ceil : V < (limit y:ℝ)+1 := Nat.lt_floor_add_one _
  have vhi : V ≤ 2*(limit y:ℝ) := by linarith [show (1:ℝ) ≤ limit y by exact_mod_cast k]
  have bound := Real.log_le_log vp vhi
  rw [lv,Real.log_mul (by norm_num) kp.ne'] at bound
  change 1 ≤ limit y ∧ L-Real.log (limit y) ≤ R+Real.log 2 ∧ L ≤ 2*Real.log (limit y)
  exact ⟨k,by linarith,by nlinarith [mul_nonneg (by linarith : 0 ≤ R-5) (by linarith : 0 ≤ R+3)]⟩

theorem limit_inf : Tendsto limit atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [sandwich,logs.eventually_ge_atTop (2*Real.log (b+1:ℕ))] with y h hl
  change 2*Real.log (b+1:ℕ) ≤ Real.log (y:ℝ) at hl
  have cmp := (Real.log_le_log_iff (by positivity : (0:ℝ)<(b+1:ℕ))
    (by exact_mod_cast h.1 : (0:ℝ)<limit y)).mp (show Real.log (b+1:ℕ) ≤ Real.log (limit y) by linarith [h.2.2])
  exact (Nat.le_succ b).trans (by exact_mod_cast cmp)

theorem small_loss : (fun y : ℕ => Real.log y-Real.log (limit y)) =o[atTop]
    (fun y => Real.log (limit y)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  filter_upwards [sandwich,roots.eventually_ge_atTop (max 2 (4/ε)),eventually_ge_atTop (2:ℕ)]
    with y h root hy
  let R := Real.sqrt (Real.log y)
  change max 2 (4/ε) ≤ R at root
  have r2 := (le_max_left _ _).trans root
  have ratio := (div_le_iff₀ he).mp ((le_max_right _ _).trans root)
  have sq : R^2=Real.log y := Real.sq_sqrt (Real.log_natCast_nonneg _)
  have le := Real.log_le_log (by exact_mod_cast h.1 : (0:ℝ)<limit y)
    (show (limit y:ℝ) ≤ y by exact_mod_cast below y)
  have low := Real.log_nonneg (show (1:ℝ) ≤ limit y by exact_mod_cast h.1)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr le),abs_of_nonneg low]
  have top : Real.log y-Real.log (limit y) ≤ R+Real.log 2 := h.2.1
  nlinarith [mul_le_mul_of_nonneg_right ratio (by linarith : 0 ≤ R),
    mul_le_mul_of_nonneg_left h.2.2 he.le,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

theorem beats_log_powers (k : ℕ) : (fun y : ℕ => (limit y:ℝ)*(Real.log y)^k)
    =o[atTop] (fun y : ℕ => (y:ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  have bound := (Real.isLittleO_pow_exp_atTop (n := 2*k)).bound he
  filter_upwards [roots.eventually bound] with y h
  let R := Real.sqrt (Real.log (y:ℝ))
  have rp : 0 ≤ R := Real.sqrt_nonneg _
  have sq : R^2=Real.log y := Real.sq_sqrt (Real.log_natCast_nonneg _)
  change ‖R^(2*k)‖ ≤ ε*‖Real.exp R‖ at h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg rp _),abs_of_pos (Real.exp_pos _),
    pow_mul,sq] at h
  have floor : (limit y:ℝ) ≤ (y:ℝ)/Real.exp R := Nat.floor_le (by positivity)
  have logn : 0 ≤ (Real.log (y:ℝ))^k := pow_nonneg (Real.log_natCast_nonneg _) _
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) logn),abs_of_nonneg (Nat.cast_nonneg _)]
  calc _ ≤ ((y:ℝ)/Real.exp R)*(ε*Real.exp R) := mul_le_mul floor h logn (by positivity)
       _ = _ := by field_simp

/-- Every fixed logarithmic saving holds for the same choice of cutoff,
    while it still admits o(H/log H) exceptional positions. -/
theorem inverse (poly : Troncature687.Cubic) :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((Transfert687.survivors (limit (full H)) H (a H)).card:ℝ))
      =o[atTop] (fun H : ℕ => (H:ℝ)/Real.log H) ∧ ∀ k : ℕ,
      (fun H : ℕ => (limit (full H):ℝ)*(Real.log (full H))^k)
        =o[atTop] (fun H : ℕ => (full H:ℝ)) := by
  obtain ⟨a,ha⟩ := Troncature687.general_inverse poly (fun H => limit (full H)) (limit_inf.comp full_inf)
    (Eventually.of_forall fun H => below (full H)) (small_loss.comp_tendsto full_inf)
  exact ⟨a,ha,fun k => (beats_log_powers k).comp_tendsto full_inf⟩

end SousExponentiel687
