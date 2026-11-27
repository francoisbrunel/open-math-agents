import Troncature687
import Profil687

/-! Quantitative exceptional counts in the inverse comparison. -/
namespace Taux687
open Presque687 Transfert687 Progressions687

noncomputable def relative (x H : ℕ) : ℝ := (holes x H:ℝ)*Real.log H/H
noncomputable def constant : ℝ := (2400*Real.exp 6)^2

theorem uniform {x H : ℕ} (big : 256 ≤ H) (cap : H ≤ x^8) :
    relative x H ≤ 17 := by
  have e := Accroissements687.extreme big cap (fun _ => 0)
  have embed : (survivors x H (fun _ => 1)).card ≤ (siftedIndices x H (fun _ => 0)).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => n-1)
    · intro n hn
      obtain ⟨interval,avoid⟩ := Finset.mem_filter.mp hn
      obtain ⟨lo,up⟩ := Finset.mem_Icc.mp interval
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by change n-1<H; omega),?_⟩
      intro p hp clash
      have h := (show n-1 ≡ 0 [MOD p] from clash).add_right 1
      apply avoid p hp
      change n ≡ 1 [MOD p]
      simpa only [Nat.sub_add_cancel lo,zero_add] using h
    · intro n hn m hm eqn
      have lo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      have lo' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
      change n-1=m-1 at eqn
      omega
  have r := (show (holes x H:ℝ) ≤ (siftedIndices x H (fun _ => 0)).card by
    exact_mod_cast (holes_le x H _).trans embed).trans e
  have lh := Real.log_pos (show (1:ℝ)<H by exact_mod_cast (show 1<H by omega))
  exact (div_le_iff₀ (by positivity : (0:ℝ)<H)).mpr ((le_div_iff₀ lh).mp r)

private theorem relative_nonneg (x H : ℕ) : 0 ≤ relative x H :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) (Nat.cast_nonneg _)

/-- Uniform form of the two-divisor bound for arbitrary interval lengths,
    including lengths beyond the finite band estimate's narrow range. -/
theorem square_profile {x H : ℕ} (size : 2 ≤ x) (big : 256 ≤ H) (xh : x ≤ H) (cap : H ≤ x^8) :
    (relative x H)^2*Real.log H ≤ constant*(Real.log H-Real.log x+Real.log (Real.log H)+4) := by
  let B := H/x+1
  let J := B*x
  let W := max 4 (max B ⌈Real.log (J:ℝ)⌉₊)
  have xp : (0:ℝ)<x := by positivity
  have hp : (0:ℝ)<H := by positivity
  have hl := Real.log_pos (show (1:ℝ)<H by exact_mod_cast (show 1<H by omega))
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast size)
  have xhn := Real.log_le_log xp (show (x:ℝ) ≤ H by exact_mod_cast xh)
  have h4 : 1 ≤ Real.log (H:ℝ) := by
    have up := Real.log_le_log (by norm_num : (0:ℝ)<4) (show (4:ℝ) ≤ H by exact_mod_cast (show 4 ≤ H by omega))
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at up
    norm_num at up
    linarith [Real.log_two_gt_d9]
  have ll := Real.log_nonneg h4
  have lo : H ≤ J := (Nat.div_lt_iff_lt_mul (by omega : 0<x)).mp (Nat.lt_succ_self (H/x)) |>.le
  have hi : J ≤ 2*H := by
    have nat := Nat.div_mul_le_self H x
    dsimp [J,B]; rw [Nat.add_mul]; omega
  have jl := Real.log_le_log hp (show (H:ℝ) ≤ J by exact_mod_cast lo)
  have jpos : (0:ℝ)<J := by exact_mod_cast (show 0<J by omega)
  have lxj := Real.log_le_log jpos (show (J:ℝ) ≤ 2*H by exact_mod_cast hi)
  rw [Real.log_mul (by norm_num) hp.ne'] at lxj
  have l2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have w4 : 4 ≤ W := le_max_left .. 
  have bw : B ≤ W := (le_max_left ..).trans (le_max_right ..)
  have base : Real.log (J:ℝ) ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right B ⌈Real.log (J:ℝ)⌉₊).trans (le_max_right 4 _))
  let A := Real.log (H:ℝ)-Real.log x+Real.log (Real.log H)+4
  have wlog : Real.log (W:ℝ) ≤ A := by
    have bpos : 0<B := Nat.succ_pos _
    have bLog := Real.log_le_log jpos (show (J:ℝ) ≤ 2*H by exact_mod_cast hi)
    have jcast : (J:ℝ) = (B:ℝ)*x := by simp [J]
    rw [jcast,Real.log_mul (by positivity) xp.ne',Real.log_mul (by norm_num) hp.ne'] at bLog
    have cj : (⌈Real.log (J:ℝ)⌉₊:ℝ) ≤ 4*Real.log H := by
      linarith [Nat.ceil_lt_add_one (hl.le.trans jl)]
    have low : 0<⌈Real.log (J:ℝ)⌉₊ := Nat.ceil_pos.mpr (hl.trans_le jl)
    have up := Real.log_le_log (by positivity : (0:ℝ)<⌈Real.log (J:ℝ)⌉₊) cj
    rw [Real.log_mul (by norm_num) hl.ne'] at up
    have c4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    rcases le_total B ⌈Real.log (J:ℝ)⌉₊ with h | h
    · simp only [W,max_eq_right h]
      rcases le_total 4 ⌈Real.log (J:ℝ)⌉₊ with z | z
      · rw [max_eq_right z]; dsimp [A]; linarith
      · rw [max_eq_left z]; norm_num; dsimp [A]; linarith
    · simp only [W,max_eq_left h]
      rcases le_total 4 B with z | z
      · rw [max_eq_right z]; dsimp [A]; linarith
      · rw [max_eq_left z]; norm_num; dsimp [A]; linarith
  have wp : (0:ℝ)<W := by exact_mod_cast (show 0<W by omega)
  have uw := Real.log_nonneg (show (1:ℝ) ≤ W by exact_mod_cast (show 1 ≤ W by omega))
  have cp : 0 ≤ constant := sq_nonneg _
  have jlog := hl.trans_le jl
  by_cases narrow : W ≤ x ∧ 64*Real.log W ≤ Real.log (J:ℝ)
  · have jcast : (J:ℝ) = (B:ℝ)*x := by simp [J]
    have pr := Profil687.explicit (B := B) (x := x) (W := W) (by omega : 2 ≤ J)
      w4 bw narrow.1 (by rw [← jcast]; exact base) (by rw [← jcast]; exact narrow.2)
    rw [← jcast] at pr
    let v := Real.sqrt (Real.log W*Real.log J)
    have vp : 0 ≤ v := Real.sqrt_nonneg _
    have vsq : v^2=Real.log W*Real.log J := Real.sq_sqrt (mul_nonneg uw jlog.le)
    have sub : (holes x H:ℝ) ≤ holes x J := by exact_mod_cast SousPuissance687.holes_mono (x := x) lo
    have ratio : (J:ℝ)/Real.log J ≤ 2*H/Real.log H :=
      (div_le_div_of_nonneg_left (by positivity) hl jl).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hi) hl.le)
    have upper : (holes x H:ℝ) ≤ (2400*Real.exp 6*v/Real.log J)*(H/Real.log H) := by
      calc _ ≤ _ := sub.trans pr
           _ ≤ 1200*Real.exp 6*(2*H/Real.log H)*(v/Real.log J) :=
             mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ratio (by positivity)) (by positivity)
           _ = _ := by ring
    have cross := (le_div_iff₀ hl).mp (show (holes x H:ℝ) ≤ (2400*Real.exp 6*v/Real.log J)*H/Real.log H
      by simpa only [mul_div_assoc] using upper)
    have norm : relative x H ≤ (2400*Real.exp 6*v)/Real.log J := (div_le_iff₀ hp).mpr cross
    have raw := (le_div_iff₀ jlog).mp norm
    have pow := pow_le_pow_left₀ (mul_nonneg (relative_nonneg x H) jlog.le) raw 2
    have cancel : ((relative x H)^2*Real.log J)*Real.log J ≤ (constant*Real.log W)*Real.log J := by
      calc _ = (relative x H*Real.log J)^2 := by ring
           _ ≤ _ := pow
           _ = _ := by dsimp [constant]; rw [mul_pow,vsq]; ring
    exact ((mul_le_mul_of_nonneg_left jl (sq_nonneg _)).trans (le_of_mul_le_mul_right cancel jlog)).trans
      (mul_le_mul_of_nonneg_left wlog cp)
  · have hw : Real.log (H:ℝ) ≤ 64*Real.log W := by
      by_cases top : W ≤ x
      · exact jl.trans (le_of_not_ge (fun h => narrow ⟨top,h⟩))
      · have wx := Real.log_le_log xp (show (x:ℝ) ≤ W by exact_mod_cast (Nat.le_of_not_ge top))
        have pow := Real.log_le_log hp (show (H:ℝ) ≤ (x:ℝ)^8 by exact_mod_cast cap)
        rw [Real.log_pow] at pow; norm_num at pow; linarith
    have r := pow_le_pow_left₀ (relative_nonneg x H) (uniform big cap) 2
    have cc : 17^2*64 ≤ constant := by
      have ex := Real.add_one_le_exp (6:ℝ)
      dsimp [constant]; nlinarith [sq_nonneg (Real.exp 6-7)]
    calc _ ≤ 17^2*(64*Real.log W) := mul_le_mul r hw hl.le (by norm_num)
         _ = (17^2*64)*Real.log W := by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_right cc uw).trans (mul_le_mul_of_nonneg_left wlog cp)

/-- Cube-root rate in the inverse comparison. At x=f(H)/log f(H),
    the quantity on the right is O(log log H). -/
theorem cube_profile {x y H : ℕ} (size : 2 ≤ x) (big : 256 ≤ H) (xy : x ≤ y)
    (yh : y ≤ H) (cap : H ≤ x^8) (full : H ≤ Erdos687.Y y) :
    (relative x H)^3*Real.log H ≤ 320*constant*
      (Real.log y-Real.log x+Real.log (Real.log H)+20) := by
  let D := relative x H
  let S := Real.log (y:ℝ)-Real.log x+10
  let L := Real.log (H:ℝ)
  have dn : 0 ≤ D := relative_nonneg x H
  have du : D ≤ 17 := uniform big cap
  have hp : (0:ℝ)<H := by positivity
  have lpos : 0<L := Real.log_pos (show (1:ℝ)<H by exact_mod_cast (show 1<H by omega))
  have l1 : 1 ≤ L := by
    have lb := Real.log_le_log (by norm_num : (0:ℝ)<4) (show (4:ℝ) ≤ H by exact_mod_cast (show 4 ≤ H by omega))
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at lb
    norm_num at lb; dsimp [L]; linarith [Real.log_two_gt_d9]
  have ll := Real.log_nonneg l1
  have sign := Real.log_le_log (by positivity : (0:ℝ)<x) (show (x:ℝ) ≤ y by exact_mod_cast xy)
  have sp : 0 ≤ S := by dsimp [S]; linarith
  have cp : 0 ≤ constant := sq_nonneg _
  change D^3*L ≤ 320*constant*(Real.log y-Real.log x+Real.log L+20)
  by_cases dpos : 0 < D
  · have many : D*((H:ℝ)/Real.log H) ≤ holes x H := by
      change (((holes x H:ℝ)*Real.log H/H)*(H/Real.log H)) ≤ _
      have nz : Real.log (H:ℝ) ≠ 0 := lpos.ne'
      field_simp <;> exact le_rfl
    have far := Troncature687.length_if_many dpos size xy yh cap full many
    change L-Real.log x ≤ (1+272/D)*S+Real.log 256 at far
    have f := mul_le_mul_of_nonneg_left far dn
    have eqn : D*((1+272/D)*S+Real.log 256) = D*S+272*S+D*Real.log 256 := by field_simp
    rw [eqn] at f
    have l256 : Real.log 256 ≤ 8 := by
      rw [show (256:ℝ)=2^8 by norm_num,Real.log_pow]; norm_num
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have c1 := mul_le_mul_of_nonneg_right du sp
    have c2 := mul_le_mul_of_nonneg_right du ll
    have c3 := mul_le_mul_of_nonneg_left l256 dn
    have coeff : D*(L-Real.log x+Real.log L+4) ≤ 320*(S+Real.log L+10) := by
      nlinarith only [f,c1,c2,c3,du,sp,ll]
    have sq := square_profile size big (xy.trans yh) cap
    change D^2*L ≤ constant*(L-Real.log x+Real.log L+4) at sq
    calc _ = D*(D^2*L) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left sq dn
         _ = constant*(D*(L-Real.log x+Real.log L+4)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left coeff cp
         _ = _ := by dsimp [S]; ring
  · have dz : D=0 := by linarith
    rw [dz]; simp only [zero_pow (by decide : 3 ≠ 0),zero_mul]
    have h : 0 ≤ Real.log y-Real.log x+Real.log L+20 := by linarith
    positivity

end Taux687
