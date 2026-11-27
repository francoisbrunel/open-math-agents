import Restes687

/-! Choose the logarithm of the intermediate cutoff geometrically
    between the logarithms of W and H. -/
namespace Profil687
open Presque687

/-- Uniform explicit exceptional count. Here W may be the maximum of
    B, 4 and the ceiling of log H. The assumptions are finite tests. -/
theorem explicit {B x W : ℕ} (hH : 2 ≤ B*x) (hW : 4 ≤ W) (bw : B ≤ W) (wx : W ≤ x)
    (base : Real.log (B*x:ℝ) ≤ W) (sep : 64*Real.log W ≤ Real.log (B*x:ℝ)) :
    (holes x (B*x):ℝ) ≤ 1200*Real.exp 6*((B*x:ℝ)/Real.log (B*x:ℝ))*
      (Real.sqrt (Real.log W*Real.log (B*x:ℝ))/Real.log (B*x:ℝ)) := by
  let H := B*x
  let L := Real.log (H:ℝ)
  let U := Real.log (W:ℝ)
  let v := Real.sqrt (U*L)
  let Z := ⌊Real.exp v⌋₊
  have cast : (H:ℝ) = (B:ℝ)*x := by simp [H]
  rw [← cast] at base sep ⊢
  have u1 : 1 ≤ U := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 4)
      (show (4:ℝ) ≤ W by exact_mod_cast hW)
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow] at h
    norm_num at h
    dsimp [U]; linarith [Real.log_two_gt_d9]
  have lpos : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  change 64*U ≤ L at sep
  have uv : 0 ≤ U := by linarith
  have vpos : 0 < v := Real.sqrt_pos.mpr (mul_pos (by linarith) lpos)
  have square : v^2 = U*L := Real.sq_sqrt (mul_nonneg uv lpos.le)
  have vlo : 8*U ≤ v := by nlinarith [mul_le_mul_of_nonneg_left sep uv]
  have vhi : v ≤ L/8 := by nlinarith [mul_le_mul_of_nonneg_right sep lpos.le]
  have fl : Real.exp v < (Z:ℝ)+1 := Nat.lt_floor_add_one _
  have half : 2 ≤ Real.exp (v/2) := by linarith [Real.add_one_le_exp (v/2)]
  have expsq : Real.exp v = Real.exp (v/2)^2 := by rw [pow_two,← Real.exp_add,add_halves]
  have zlo : v/2 ≤ Real.log (Z:ℝ) := by
    calc _ = Real.log (Real.exp (v/2)) := (Real.log_exp _).symm
         _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by nlinarith)
  have zpos : (0:ℝ) < Z := by linarith [Real.add_one_le_exp v]
  have zhi : Real.log (Z:ℝ) ≤ v := by
    calc _ ≤ Real.log (Real.exp v) := Real.log_le_log zpos (Nat.floor_le (Real.exp_nonneg _))
         _ = _ := Real.log_exp _
  have wz : W ≤ Z := by
    exact_mod_cast (Real.log_le_log_iff (by positivity : (0:ℝ) < W) zpos).mp (by change U ≤ _; linarith)
  have bpos : 0 < B := by
    by_contra! h
    have zero : B = 0 := by omega
    simp [zero] at hH
  have xs : 4 ≤ x := by omega
  have xpos : (0:ℝ) < x := by positivity
  have lx : L ≤ 2*Real.log (x:ℝ) := by
    dsimp [L]; rw [cast,Real.log_mul (by positivity) xpos.ne']
    linarith [Real.log_le_log (by positivity : (0:ℝ)<B)
      (show (B:ℝ) ≤ x by exact_mod_cast bw.trans wx)]
  have zx : Z ≤ x := by
    exact_mod_cast (Real.log_le_log_iff zpos xpos).mp (by linarith)
  have room : Z^2*W^5 ≤ H := by
    have val : Real.log ((Z^2*W^5:ℕ):ℝ) = 2*Real.log Z+5*U := by
      dsimp [U]; push_cast
      rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]; norm_num
    have cmp : Real.log ((Z^2*W^5:ℕ):ℝ) ≤ L := by rw [val]; linarith
    have zNat : 0 < Z := by omega
    have wNat : 0 < W := by omega
    exact_mod_cast (Real.log_le_log_iff (by positivity : (0:ℝ) < (Z^2*W^5:ℕ))
      (by exact_mod_cast (show 0 < H by omega) : (0:ℝ)<H)).mp cmp
  have h := Restes687.band_estimate hH hW bw wz zx room
    (by rw [← cast]; change _ ≤ L/4; linarith) (by rw [← cast]; exact base)
  rw [← cast] at h
  have logz : 0 < Real.log (Z:ℝ) := by linarith
  have rat : U/Real.log Z ≤ 2*v/L := by
    apply (div_le_div_iff₀ logz lpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left zlo vpos.le]
  have rat' := div_le_div_of_nonneg_right zhi lpos.le
  have combined : U/Real.log Z+Real.log Z/L ≤ 3*(v/L) := by
    calc _ ≤ 2*v/L+v/L := add_le_add rat rat'
         _ = _ := by ring
  refine h.trans ?_
  change ((H:ℝ)/L)*(400*Real.exp 6)*(U/Real.log Z+Real.log Z/L) ≤ _
  calc _ ≤ ((H:ℝ)/L)*(400*Real.exp 6)*(3*(v/L)) := mul_le_mul_of_nonneg_left combined (by positivity)
       _ = _ := by change _ = 1200*Real.exp 6*((H:ℝ)/L)*(v/L); ring

end Profil687
