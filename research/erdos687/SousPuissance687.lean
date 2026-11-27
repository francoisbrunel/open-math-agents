import Restes687

/-! Every multiplier with log B = o(log x) admits an almost-cover of
    [1,Bx] with o(Bx/log(Bx)) exceptions. -/
namespace SousPuissance687
open Filter Presque687
open scoped Asymptotics

noncomputable def cut (a : ℝ) (H : ℕ) : ℕ := ⌊Real.exp (a*Real.log H)⌋₊

private theorem cutoff_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ H : ℕ in atTop, 4 ≤ cut a H ∧
      a*Real.log H/2 ≤ Real.log (cut a H) ∧ Real.log (cut a H) ≤ a*Real.log H ∧
      Real.log H ≤ (cut a H:ℝ) := by
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  have slow := Real.isLittleO_log_id_atTop.bound (show 0 < a/2 by positivity)
  filter_upwards [logs.eventually_ge_atTop (max 2 (8/a)),logs.eventually slow] with H hh hslow
  let L := Real.log (H:ℝ)
  change max 2 (8/a) ≤ L at hh
  have l2 := (le_max_left _ _).trans hh
  have al := (div_le_iff₀ ha).mp ((le_max_right _ _).trans hh)
  have big : 4 ≤ cut a H := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    (by change (4:ℝ) ≤ Real.exp (a*L); linarith [Real.add_one_le_exp (a*L)])
  have half : 2 ≤ Real.exp (a*L/2) := by linarith [Real.add_one_le_exp (a*L/2)]
  have square : Real.exp (a*L) = Real.exp (a*L/2)^2 := by
    rw [pow_two,← Real.exp_add,add_halves]
  have floor : Real.exp (a*L) < (cut a H:ℝ)+1 := Nat.lt_floor_add_one _
  have halfFloor : Real.exp (a*L/2) ≤ (cut a H:ℝ) := by nlinarith
  have hi : Real.log (cut a H) ≤ a*L := by
    calc _ ≤ Real.log (Real.exp (a*L)) := Real.log_le_log (by positivity) (Nat.floor_le (Real.exp_nonneg _))
         _ = _ := Real.log_exp _
  have slow' : Real.log L ≤ a*L/2 := by
    change ‖Real.log L‖ ≤ (a/2)*‖L‖ at hslow
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith)),
      abs_of_nonneg (by linarith : 0 ≤ L)] at hslow
    linarith
  refine ⟨big,?_,hi,?_⟩
  · calc a*L/2 = Real.log (Real.exp (a*L/2)) := (Real.log_exp _).symm
         _ ≤ _ := Real.log_le_log (Real.exp_pos _) halfFloor
  · calc L = Real.exp (Real.log L) := (Real.exp_log (by linarith)).symm
         _ ≤ _ := (Real.exp_le_exp.mpr slow').trans halfFloor

/-- The two logarithmic losses in the finite band estimate can be made
    arbitrarily small, uniformly for bounded or unbounded multipliers. -/
theorem almost_cover_along (X B : ℕ → ℕ) (xinf : Tendsto X atTop atTop) (one : ∀ᶠ x : ℕ in atTop, 1 ≤ B x)
    (small : (fun x : ℕ => Real.log (B x)) =o[atTop] (fun x : ℕ => Real.log (X x))) :
    (fun x : ℕ => (holes (X x) (B x*X x):ℝ)) =o[atTop]
      (fun x : ℕ => ((B x*X x:ℕ):ℝ)/Real.log (B x*X x:ℕ)) := by
  let H := fun i : ℕ => B i*X i
  have inf : Tendsto H atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [one,xinf.eventually_ge_atTop b] with i h hx
    exact hx.trans (by simpa [H] using Nat.mul_le_mul_right (X i) h)
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  let D : ℝ := 400*Real.exp 6
  have hD : 0 < D := by dsimp [D]; positivity
  let a : ℝ := min (1/8) (ε/(3*D))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have eighth : a ≤ 1/8 := min_le_left .. 
  have eps := (le_div_iff₀ (by positivity : 0 < 3*D)).mp (min_le_right (1/8:ℝ) (ε/(3*D)))
  change a*(3*D) ≤ ε at eps
  have aa : a^2 ≤ a := by nlinarith [mul_nonneg ha.le (show 0 ≤ 1-a by linarith)]
  have sumexp : 2*a+5*a^2 ≤ 1 := by nlinarith
  have band := small.bound (show 0 < a^2/2 by positivity)
  filter_upwards [one,band,xinf.eventually_ge_atTop (2:ℕ),inf.eventually (cutoff_bounds ha),
    inf.eventually (cutoff_bounds (sq_pos_of_pos ha))] with i hB hsmall hx hz hw
  let Z := cut a (H i)
  let W := cut (a^2) (H i)
  let L := Real.log (H i:ℝ)
  let Lx := Real.log ((X i):ℝ)
  change 4 ≤ Z ∧ a*L/2 ≤ Real.log Z ∧ Real.log Z ≤ a*L ∧ L ≤ (Z:ℝ) at hz
  change 4 ≤ W ∧ a^2*L/2 ≤ Real.log W ∧ Real.log W ≤ a^2*L ∧ L ≤ (W:ℝ) at hw
  obtain ⟨z4,zlo,zhi,_⟩ := hz
  obtain ⟨w4,wlo,whi,wbase⟩ := hw
  have xx := Real.log_pos (show (1:ℝ) < (X i) by exact_mod_cast hx)
  have hxH : (X i) ≤ H i := by simpa [H] using Nat.mul_le_mul_right (X i) hB
  have hn := hx.trans hxH
  have lpos : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < H i by omega))
  have xlo : Lx ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hxH)
  have bpos : (0:ℝ) < B i := by exact_mod_cast hB
  have blog : 0 ≤ Real.log (B i:ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  change ‖Real.log (B i:ℝ)‖ ≤ a^2/2*‖Lx‖ at hsmall
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg blog,abs_of_nonneg xx.le] at hsmall
  have bw : B i ≤ W := by
    have l := mul_le_mul_of_nonneg_left xlo (show 0 ≤ a^2/2 by positivity)
    exact_mod_cast (Real.log_le_log_iff bpos (by positivity : (0:ℝ) < W)).mp (by linarith)
  have wz : W ≤ Z := Nat.floor_mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right aa lpos.le))
  have logH : L = Real.log (B i:ℝ)+Lx := by
    dsimp [L,H,Lx]; rw [Nat.cast_mul,Real.log_mul bpos.ne' (by positivity)]
  have xl : L ≤ 2*Lx := by
    have x0 : 0 ≤ Lx := xx.le
    nlinarith [mul_le_mul_of_nonneg_right (show a^2/2 ≤ 1 by linarith) x0]
  have zx : Z ≤ (X i) := by
    have bound : a*L ≤ Lx := by
      nlinarith [mul_le_mul_of_nonneg_right eighth lpos.le]
    exact_mod_cast (Real.log_le_log_iff (by positivity : (0:ℝ) < Z) (by positivity : (0:ℝ) < (X i))).mp
      (zhi.trans bound)
  have room : Z^2*W^5 ≤ H i := by
    have lhs : Real.log ((Z^2*W^5:ℕ):ℝ) = 2*Real.log Z+5*Real.log W := by
      push_cast; rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]; norm_num
    have cmp : Real.log ((Z^2*W^5:ℕ):ℝ) ≤ L := by
      rw [lhs]
      nlinarith [mul_le_mul_of_nonneg_right sumexp lpos.le]
    exact_mod_cast (Real.log_le_log_iff (by positivity : (0:ℝ) < (Z^2*W^5:ℕ))
      (by positivity : (0:ℝ) < H i)).mp cmp
  have scale : Real.log Z ≤ L/4 := by nlinarith [mul_le_mul_of_nonneg_right eighth lpos.le]
  have cast : (H i:ℝ) = (B i:ℝ)*(X i) := by simp [H]
  have bound := Restes687.band_estimate hn w4 bw wz zx room
    (by simpa [← cast,L] using scale) (by simpa [← cast,L] using wbase)
  rw [← cast] at bound
  have zpos := Real.log_pos (show (1:ℝ) < Z by exact_mod_cast (show 1 < Z by omega))
  have r₁ : Real.log W/Real.log Z ≤ 2*a := (div_le_iff₀ zpos).mpr
    (by nlinarith [mul_le_mul_of_nonneg_left zlo (show 0 ≤ 2*a by positivity)])
  have r₂ : Real.log Z/L ≤ a := (div_le_iff₀ lpos).mpr zhi
  have coeff : D*(Real.log W/Real.log Z+Real.log Z/L) ≤ ε := by
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add r₁ r₂) hD.le]
  have nn : 0 ≤ (H i:ℝ)/L := div_nonneg (by positivity) lpos.le
  change ‖(holes (X i) (H i):ℝ)‖ ≤ ε*‖(H i:ℝ)/L‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg nn]
  calc
    _ ≤ _ := bound
    _ = (D*(Real.log W/Real.log Z+Real.log Z/L))*((H i:ℝ)/L) := by dsimp [D,L]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coeff nn

theorem almost_cover (B : ℕ → ℕ) (one : ∀ᶠ x : ℕ in atTop, 1 ≤ B x)
    (small : (fun x : ℕ => Real.log (B x)) =o[atTop] (fun x : ℕ => Real.log x)) :
    (fun x : ℕ => (holes x (B x*x):ℝ)) =o[atTop]
      (fun x : ℕ => ((B x*x:ℕ):ℝ)/Real.log (B x*x:ℕ)) :=
  almost_cover_along id B tendsto_id one small

theorem holes_mono {x h H : ℕ} (le : h ≤ H) : holes x h ≤ holes x H := by
  obtain ⟨a,ha⟩ := realizes x H
  rw [← ha]
  apply (holes_le x h a).trans (Finset.card_le_card ?_)
  intro n hn
  obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
  obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨lo,up.trans le⟩,avoid⟩

/-- The interval need not be a multiple of x. The conclusion supplies
    actual residue classes for each x. -/
theorem arbitrary_length_along (X H : ℕ → ℕ) (xinf : Tendsto X atTop atTop) (large : ∀ᶠ x : ℕ in atTop, X x ≤ H x)
    (scale : (fun x : ℕ => Real.log (H x)-Real.log (X x)) =o[atTop] (fun x : ℕ => Real.log (X x))) :
    ∃ a : ℕ → ℕ → ℕ, (fun x => ((Transfert687.survivors (X x) (H x) (a x)).card:ℝ)) =o[atTop]
      (fun x => (H x:ℝ)/Real.log (H x)) := by
  let B := fun i => H i/X i+1
  have one : ∀ i, 1 ≤ B i := fun _ => Nat.succ_pos _
  have logInf := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)).comp xinf
  have compare (i : ℕ) (hx : 2 ≤ (X i)) (hle : (X i) ≤ H i) :
      H i ≤ B i*(X i) ∧ B i*(X i) ≤ 2*H i := by
    have up := Nat.div_mul_le_self (H i) (X i)
    have lo := (Nat.div_lt_iff_lt_mul (by omega : 0 < (X i))).mp (Nat.lt_succ_self (H i/(X i)))
    refine ⟨lo.le,?_⟩
    dsimp [B]; rw [Nat.add_mul]; omega
  have bsmall : (fun i : ℕ => Real.log (B i)) =o[atTop] (fun i : ℕ => Real.log (X i)) := by
    apply Asymptotics.isLittleO_iff.mpr
    intro ε he
    filter_upwards [large,xinf.eventually_ge_atTop (2:ℕ),scale.bound (half_pos he),
      logInf.eventually_ge_atTop (2*Real.log 2/ε)] with i hle hx hs hl
    have Lx := Real.log_pos (show (1:ℝ) < (X i) by exact_mod_cast hx)
    have hp : (0:ℝ) < H i := by exact_mod_cast (show 0 < H i by omega)
    have bp : 0 < (B i:ℝ) := by exact_mod_cast one i
    have logle := Real.log_le_log (show (0:ℝ) < (X i) by positivity) (show ((X i):ℝ) ≤ H i by exact_mod_cast hle)
    have cc : (B i:ℝ)*(X i) ≤ 2*(H i:ℝ) := by exact_mod_cast (compare i hx hle).2
    have sum := Real.log_le_log (show 0 < (B i:ℝ)*(X i) by positivity) cc
    rw [Real.log_mul bp.ne' (by positivity),Real.log_mul (by norm_num) hp.ne'] at sum
    change 2*Real.log 2/ε ≤ Real.log ((X i):ℝ) at hl
    have lim := (div_le_iff₀ he).mp hl
    change ‖Real.log (H i)-Real.log (X i)‖ ≤ ε/2*‖Real.log ((X i):ℝ)‖ at hs
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr logle),abs_of_nonneg Lx.le] at hs
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast one i)),
      abs_of_nonneg Lx.le]
    linarith
  have near := almost_cover_along X B xinf (Eventually.of_forall one) bsmall
  choose a ha using fun i => realizes (X i) (H i)
  refine ⟨a,Asymptotics.isLittleO_iff.mpr ?_⟩
  intro ε he
  filter_upwards [large,xinf.eventually_ge_atTop (2:ℕ),near.bound (half_pos he)] with i hle hx hb
  obtain ⟨lo,up⟩ := compare i hx hle
  have lh := Real.log_pos (show (1:ℝ) < H i by exact_mod_cast (show 1 < H i by omega))
  have logs := Real.log_le_log (show (0:ℝ) < H i by exact_mod_cast (show 0 < H i by omega))
    (show (H i:ℝ) ≤ (B i*(X i):ℕ) by exact_mod_cast lo)
  have lr : 0 ≤ Real.log ((B i*(X i):ℕ):ℝ) := lh.le.trans logs
  have cb : ((B i*(X i):ℕ):ℝ)/Real.log (B i*(X i):ℕ) ≤ (2*(H i:ℝ))/Real.log (H i) :=
    (div_le_div_of_nonneg_left (by positivity) lh logs).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast up) lh.le)
  change ‖(holes (X i) (B i*(X i)):ℝ)‖ ≤ ε/2*‖((B i*(X i):ℕ):ℝ)/Real.log (B i*(X i):ℕ)‖ at hb
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (div_nonneg (by positivity) lr)] at hb
  have bound := (show (holes (X i) (H i):ℝ) ≤ holes (X i) (B i*(X i)) by exact_mod_cast holes_mono (x := (X i)) lo).trans
    (hb.trans (mul_le_mul_of_nonneg_left cb (half_pos he).le))
  rw [ha,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (div_nonneg (by positivity) lh.le)]
  exact bound.trans_eq (by ring)

theorem arbitrary_length (H : ℕ → ℕ) (large : ∀ᶠ x : ℕ in atTop, x ≤ H x)
    (scale : (fun x : ℕ => Real.log (H x)-Real.log x) =o[atTop] (fun x : ℕ => Real.log x)) :
    ∃ a : ℕ → ℕ → ℕ, (fun x => ((Transfert687.survivors x (H x) (a x)).card:ℝ)) =o[atTop]
      (fun x => (H x:ℝ)/Real.log (H x)) :=
  arbitrary_length_along id H tendsto_id large scale

end SousPuissance687
