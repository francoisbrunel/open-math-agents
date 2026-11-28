import InverseNatif687
import TransfertFinNatif687

/-! The explicit obstruction to complete coverage, in Erdős's inverse
formulation with the least permissible prime cutoff. -/
namespace InverseFin687
open Filter Inverse687
open scoped Asymptotics

theorem cutoff_lower :
    (fun H : ℕ => Real.sqrt H * (Real.log H)^(401/400:ℝ)) =O[atTop]
      (fun H : ℕ => (full H:ℝ)) := by
  obtain ⟨C,hC,est⟩ := TransfertFin687.gain_one_two_hundred.exists_pos
  let a := (401/400:ℝ)
  apply Asymptotics.IsBigO.of_bound ((3:ℝ)^a*Real.sqrt C)
  have cubic := Troncature687.cubic_of_quadratic
    (Troncature687.quadratic_of_saving erdos687_log_saving)
  filter_upwards [full_inf.eventually est.bound, full_inf.eventually cubic,
    full_inf.eventually (eventually_ge_atTop (2:ℕ)),eventually_ge_atTop (2:ℕ)] with H bound size fy hH
  let x := full H
  have xp : (1:ℝ) < x := by exact_mod_cast (by change 2 ≤ x at fy; omega : 1 < x)
  have Hp : (1:ℝ) < H := by exact_mod_cast (by omega : 1 < H)
  have lp := Real.log_pos xp
  have lh := Real.log_pos Hp
  have pos : 0 < (x:ℝ) := by linarith
  have room : H ≤ x^3 := (full_spec H).trans size
  have high := Real.log_le_log (by linarith : 0 < (H:ℝ)) (by exact_mod_cast room : (H:ℝ) ≤ (x:ℝ)^3)
  rw [Real.log_pow] at high
  have logpow : (Real.log H)^a ≤ (3:ℝ)^a*(Real.log x)^a := by
    rw [← Real.mul_rpow (by norm_num) lp.le]
    exact Real.rpow_le_rpow lh.le (by simpa using high) (by dsimp [a]; norm_num)
  have hy : (H:ℝ) ≤ C*((x:ℝ)^2/(Real.log x)^(a*2)) := by
    apply le_trans (show (H:ℝ) ≤ Erdos687.Y x by exact_mod_cast full_spec H)
    change ‖(Erdos687.Y x:ℝ)‖ ≤ C*‖(x:ℝ)^2/(Real.log x)^(2+1/200:ℝ)‖ at bound
    rwa [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (by positivity),
      show (2+1/200:ℝ)=a*2 by dsimp [a]; norm_num] at bound
  rw [← mul_div_assoc] at hy
  have sq := (le_div_iff₀ (Real.rpow_pos_of_pos lp _)).1 hy
  have power : (Real.log x)^(a*2) = ((Real.log x)^a)^2 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast lp.le a 2
  rw [power] at sq
  have hn := Real.sqrt_nonneg (H:ℝ)
  have root : Real.sqrt H*(Real.log x)^a ≤ Real.sqrt C*x := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) pos.le)
    simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg H),Real.sq_sqrt hC.le] using sq
  rw [Real.norm_of_nonneg (mul_nonneg hn (Real.rpow_nonneg lh.le _)),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ Real.sqrt H*((3:ℝ)^a*(Real.log x)^a) := mul_le_mul_of_nonneg_left logpow hn
    _ = (3:ℝ)^a*(Real.sqrt H*(Real.log x)^a) := by ring
    _ ≤ (3:ℝ)^a*(Real.sqrt C*x) := mul_le_mul_of_nonneg_left root (by positivity)
    _ = _ := by change _ = ((3:ℝ)^a*Real.sqrt C)*x; ring

end InverseFin687

#print axioms InverseFin687.cutoff_lower
