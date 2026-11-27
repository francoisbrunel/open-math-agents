import Accroissements687
import Inverse687

/-! Deleting a terminal band of primes from a complete cover. -/
namespace Troncature687
open Filter Transfert687 Progressions687 Presque687
open scoped Asymptotics

/-- Restricting a complete cover at y to primes up to x costs the
    reciprocal mass of the deleted band, divided by log(H/y). -/
theorem truncate {x y H : ℕ} (size : 2 ≤ x) (xy : x ≤ y) (far : 256*y ≤ H)
    (radius : H ≤ x^8) (full : H ≤ Erdos687.Y y) :
    (holes x H:ℝ) ≤ 34*H*(Real.log y-Real.log x+10)/
      (Real.log x*(Real.log H-Real.log y)) := by
  have xp : (0:ℝ) < x := by positivity
  have yp : (0:ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  let L := Real.log (H:ℝ)-Real.log (y:ℝ)
  have lpos : 0 < L := sub_pos.mpr (Real.log_lt_log yp
    (show (y:ℝ)<H by exact_mod_cast (show y<H by omega)))
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast size)
  obtain ⟨a,cov⟩ := Extension687.optimal_cover y
  have covered (n : ℕ) (hn : n ∈ Finset.Icc 1 H) :
      ∃ p ≤ y, p.Prime ∧ n%p = a p%p := by
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hn
    exact cov n (Finset.mem_Icc.mpr ⟨lo,up.trans full⟩)
  have sum := OMA.R_Erdos687_erdos_687_variants_iwaniec_R2.survivor_le_sum (z := x) a covered
  change (survivors x H a).card ≤ ∑ p ∈ y.primesLE \ x.primesLE, charge (survivors x H a) a p at sum
  have term (p : ℕ) (mem : p ∈ y.primesLE \ x.primesLE) :
      (charge (survivors x H a) a p:ℝ) ≤ (34*H/L)*(1/(p:ℝ)) := by
    obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp mem
    obtain ⟨py,pr⟩ := Nat.mem_primesLE.mp hin
    have px : x < p := by
      by_contra! le
      exact hout (Nat.mem_primesLE.mpr ⟨le,pr⟩)
    let J := H/p+1
    have pp : (0:ℝ) < p := by exact_mod_cast pr.pos
    have jm : H < J*p := (Nat.div_lt_iff_lt_mul pr.pos).mp (Nat.lt_succ_self _)
    have big : 256 ≤ J := by
      have q := (Nat.le_div_iff_mul_le pr.pos).mpr ((Nat.mul_le_mul_left 256 py).trans far)
      dsimp [J]; omega
    have cap : J ≤ x^8 := by
      have u := Nat.div_lt_self (by omega : 0 < H) pr.one_lt
      dsimp [J]; omega
    have jp : (0:ℝ) < J := by positivity
    have low : (H:ℝ)/y ≤ J := (div_le_iff₀ yp).mpr (by exact_mod_cast jm.le.trans (Nat.mul_le_mul_left J py))
    have high : (J:ℝ) ≤ 2*H/p := by
      apply (le_div_iff₀ pp).mpr
      have u := Nat.div_mul_le_self H p
      exact_mod_cast (show J*p ≤ 2*H by dsimp [J]; rw [Nat.add_mul]; omega)
    have lj := Real.log_le_log (div_pos hp yp) low
    rw [Real.log_div hp.ne' yp.ne'] at lj
    change L ≤ Real.log (J:ℝ) at lj
    obtain ⟨b,cb⟩ := charge_le_index_sieve (N := H) pr px a
    have saved := Accroissements687.extreme big cap b
    calc
      _ ≤ ((siftedIndices x J b).card:ℝ) := by exact_mod_cast cb
      _ ≤ _ := saved
      _ ≤ 17*J/L := div_le_div_of_nonneg_left (by positivity) lpos lj
      _ ≤ (17*(2*H/p))/L := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left high (by norm_num)) lpos.le
      _ = _ := by ring
  have raw := Harmonique687.band_bound (z := (x:ℝ)) (x := y) (by exact_mod_cast size) (by exact_mod_cast xy)
  rw [Nat.floor_natCast] at raw
  have band : (∑ p ∈ y.primesLE \ x.primesLE, (1:ℝ)/p) ≤
      (Real.log y-Real.log x+10)/Real.log x := (le_div_iff₀ lx).mpr (by rwa [mul_comm])
  calc
    _ ≤ ∑ p ∈ y.primesLE \ x.primesLE, (charge (survivors x H a) a p:ℝ) := by
      exact_mod_cast (holes_le x H a).trans sum
    _ ≤ _ := Finset.sum_le_sum term
    _ = (34*H/L)*(∑ p ∈ y.primesLE \ x.primesLE, (1:ℝ)/p) := (Finset.mul_sum ..).symm
    _ ≤ (34*H/L)*((Real.log y-Real.log x+10)/Real.log x) :=
      mul_le_mul_of_nonneg_left band (by positivity)
    _ = _ := by rw [div_mul_div_comm,mul_comm L (Real.log x)]

/-- If truncation leaves a fixed positive normalized exceptional count,
    then the full interval was only slightly longer on a log scale.
    The constant is independent of the interval and both cutoffs. -/
theorem length_if_many {x y H : ℕ} {ε : ℝ} (he : 0 < ε) (size : 2 ≤ x)
    (xy : x ≤ y) (yh : y ≤ H) (radius : H ≤ x^8) (full : H ≤ Erdos687.Y y)
    (many : ε*((H:ℝ)/Real.log H) ≤ holes x H) :
    Real.log H-Real.log x ≤ (1+272/ε)*(Real.log y-Real.log x+10)+Real.log 256 := by
  have xp : (0:ℝ)<x := by positivity
  have yp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast size)
  have lh := Real.log_pos (show (1:ℝ)<H by exact_mod_cast (show 1<H by omega))
  let S := Real.log (y:ℝ)-Real.log x+10
  have gap := Real.log_le_log xp (show (x:ℝ) ≤ y by exact_mod_cast xy)
  have sp : 0 ≤ S := by dsimp [S]; linarith
  have wide := Real.log_le_log hp (show (H:ℝ) ≤ (x:ℝ)^8 by exact_mod_cast radius)
  rw [Real.log_pow] at wide
  norm_num at wide
  have positive := Real.log_nonneg (show (1:ℝ) ≤ 256 by norm_num)
  by_cases far : 256*y ≤ H
  · let D := Real.log (H:ℝ)-Real.log y
    have dp : 0 < D := sub_pos.mpr (Real.log_lt_log yp (by exact_mod_cast (show y<H by omega)))
    have h := many.trans (truncate size xy far radius full)
    change ε*((H:ℝ)/Real.log H) ≤ 34*H*S/(Real.log x*D) at h
    have crossed : (ε*H)*(Real.log x*D) ≤ (34*H*S)*Real.log H :=
      (div_le_div_iff₀ lh (mul_pos lx dp)).mp (by simpa only [mul_div_assoc] using h)
    have cancel : (H:ℝ)*(ε*D*Real.log x) ≤ H*(34*S*Real.log H) := by
      nlinarith only [crossed]
    have c := (le_of_mul_le_mul_left cancel hp)
    have replace := mul_le_mul_of_nonneg_left wide (show 0 ≤ 34*S by positivity)
    have c' : (ε*D)*Real.log x ≤ (272*S)*Real.log x := by nlinarith only [c,replace]
    have last := le_of_mul_le_mul_right c' lx
    have lift : D ≤ (272/ε)*S := (le_div_iff₀ he).mpr (by nlinarith only [last]) |>.trans_eq
      (show 272*S/ε = (272/ε)*S by ring)
    dsimp [D,S] at lift
    nlinarith only [lift,positive]
  · have height := Real.log_le_log hp (show (H:ℝ) ≤ 256*y by exact_mod_cast (Nat.le_of_not_ge far))
    rw [Real.log_mul (by norm_num) yp.ne'] at height
    have extra : 0 ≤ (272/ε)*S := by positivity
    dsimp [S] at extra
    nlinarith only [height,extra]

/-- A full cover at y forces an almost-cover at every x in the same
    logarithmic scale, uniformly up to length x^8. -/
theorem remove_band (X Y H : ℕ → ℕ) (xinf : Tendsto X atTop atTop)
    (range : ∀ᶠ i : ℕ in atTop, X i ≤ Y i ∧ Y i ≤ H i ∧ H i ≤ (X i)^8 ∧ H i ≤ Erdos687.Y (Y i))
    (gap : (fun i => Real.log (Y i)-Real.log (X i)) =o[atTop] (fun i => Real.log (X i))) :
    (fun i => (holes (X i) (H i):ℝ)) =o[atTop] (fun i => (H i:ℝ)/Real.log (H i)) := by
  classical
  have logs := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)).comp xinf
  have constants (c : ℝ) : (fun _ : ℕ => c) =o[atTop] (fun i => Real.log (X i)) :=
    (Asymptotics.isLittleO_const_id_atTop c).comp_tendsto logs
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  let bad (i : ℕ) := ε*((H i:ℝ)/Real.log (H i)) ≤ holes (X i) (H i)
  let T (i : ℕ) := if bad i then H i else X i
  have xl : ∀ᶠ i : ℕ in atTop, X i ≤ T i := by
    filter_upwards [range] with i hr
    dsimp only [T]
    split <;> first | exact hr.1.trans hr.2.1 | exact le_rfl
  let C := 1+272/ε
  let major (i : ℕ) := C*(Real.log (Y i)-Real.log (X i)+10)+Real.log 256
  have small : major =o[atTop] (fun i => Real.log (X i)) :=
    (((gap.add (constants 10)).const_mul_left C).add (constants (Real.log 256)))
  have bounded : (fun i => Real.log (T i)-Real.log (X i)) =O[atTop] major := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [range,xl,xinf.eventually_ge_atTop 2] with i h ht hx
    have xp : (0:ℝ)<X i := by exact_mod_cast (show 0<X i by omega)
    have le := Real.log_le_log xp (show (X i:ℝ) ≤ T i by exact_mod_cast ht)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr le)]
    by_cases b : bad i
    · simpa only [T,if_pos b,major,C] using length_if_many he hx h.1 h.2.1 h.2.2.1 h.2.2.2 b
    · simp only [T,if_neg b,sub_self,major]
      have gy := Real.log_le_log xp (show (X i:ℝ) ≤ Y i by exact_mod_cast h.1)
      have nn : 0 ≤ Real.log (Y i)-Real.log (X i)+10 := by linarith
      have cc : 0 ≤ C := by dsimp [C]; positivity
      linarith [mul_nonneg cc nn,Real.log_nonneg (show (1:ℝ) ≤ 256 by norm_num)]
  obtain ⟨a,ha⟩ := SousPuissance687.arbitrary_length_along X T xinf xl (bounded.trans_isLittleO small)
  filter_upwards [ha.bound he,range,xinf.eventually_ge_atTop 2] with i cover hr hx
  have hh := hx.trans (hr.1.trans hr.2.1)
  have lh := Real.log_pos (show (1:ℝ)<H i by exact_mod_cast hh)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (div_nonneg (by positivity) lh.le)]
  by_cases b : bad i
  · change ‖((Transfert687.survivors (X i) (T i) (a i)).card:ℝ)‖ ≤
      ε*‖(T i:ℝ)/Real.log (T i)‖ at cover
    simp only [T,if_pos b,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) lh.le)] at cover
    exact (by exact_mod_cast holes_le (X i) (H i) (a i) :
      (holes (X i) (H i):ℝ) ≤ (Transfert687.survivors (X i) (H i) (a i)).card).trans cover
  · exact (lt_of_not_ge b).le

/-- This mild polynomial bound follows already from Iwaniec's classical
    Y(x) = O(x²). Only the displayed exponent is used by the proof. -/
def Cubic : Prop := ∀ᶠ y : ℕ in atTop, Erdos687.Y y ≤ y^3

theorem cubic_of_quadratic (quad : (fun y : ℕ => (Erdos687.Y y:ℝ)) =O[atTop]
    (fun y : ℕ => (y:ℝ)^2)) : Cubic := by
  obtain ⟨C,hc,bound⟩ := Asymptotics.isBigO_iff'.mp quad
  filter_upwards [bound,(tendsto_natCast_atTop_atTop : Tendsto (fun y : ℕ => (y:ℝ)) atTop atTop).eventually_ge_atTop C]
    with y h big
  change ‖(Erdos687.Y y:ℝ)‖ ≤ C*‖(y:ℝ)^2‖ at h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (sq_nonneg _)] at h
  exact_mod_cast (show (Erdos687.Y y:ℝ) ≤ (y:ℝ)^3 by
    nlinarith [mul_le_mul_of_nonneg_right big (sq_nonneg (y:ℝ))])

/-- Every smaller cutoff on the same logarithmic scale as the optimal
    full cutoff suffices for almost-coverage, for all large lengths. -/
theorem general_inverse (poly : Cubic) (X : ℕ → ℕ) (xinf : Tendsto X atTop atTop)
    (xf : ∀ᶠ H : ℕ in atTop, X H ≤ Inverse687.full H)
    (gap : (fun H => Real.log (Inverse687.full H)-Real.log (X H)) =o[atTop] (fun H => Real.log (X H))) :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((survivors (X H) H (a H)).card:ℝ)) =o[atTop]
      (fun H : ℕ => (H:ℝ)/Real.log H) := by
  have range : ∀ᶠ H : ℕ in atTop, X H ≤ Inverse687.full H ∧ Inverse687.full H ≤ H ∧
      H ≤ (X H)^8 ∧ H ≤ Erdos687.Y (Inverse687.full H) := by
    filter_upwards [xf,Inverse687.full_small,Inverse687.full_inf.eventually poly,
      xinf.eventually_ge_atTop 2,gap.bound (by norm_num : (0:ℝ)<1)] with H le small cap hx hl
    let f := Inverse687.full H
    let x := X H
    have xp : (0:ℝ)<x := by exact_mod_cast (show 0<X H by omega)
    have fp : (0:ℝ)<f := by exact_mod_cast (show 0<Inverse687.full H by omega)
    have hp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
    have spec := Inverse687.full_spec H
    have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast hx)
    have sign := Real.log_le_log xp (show (x:ℝ) ≤ f by exact_mod_cast le)
    change ‖Real.log f-Real.log x‖ ≤ 1*‖Real.log (x:ℝ)‖ at hl
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr sign),abs_of_nonneg lx.le] at hl
    have bound := Real.log_le_log hp (show (H:ℝ) ≤ (f:ℝ)^3 by exact_mod_cast spec.trans cap)
    rw [Real.log_pow] at bound
    have wide : Real.log (H:ℝ) ≤ Real.log ((x:ℝ)^8) := by
      rw [Real.log_pow]; norm_num at bound ⊢; linarith
    exact ⟨le,small,by exact_mod_cast (Real.log_le_log_iff hp (pow_pos xp 8)).mp wide,spec⟩
  have upper := remove_band X Inverse687.full id xinf range gap
  choose a ha using fun H => realizes (X H) H
  exact ⟨a,upper.congr_left (fun H => (congrArg (fun n : ℕ => (n:ℝ)) (ha H)).symm)⟩

/-- A factor asymptotic to log f(H) may be saved, with f(H) the least
    full cutoff. Its sole input is a classical proved polynomial bound. -/
theorem inverse_of_quadratic (quad : (fun y : ℕ => (Erdos687.Y y:ℝ)) =O[atTop]
    (fun y : ℕ => (y:ℝ)^2)) :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((survivors (Inverse687.weak H) H (a H)).card:ℝ))
      =o[atTop] (fun H : ℕ => (H:ℝ)/Real.log H) ∧
      (fun H : ℕ => (Inverse687.weak H:ℝ)) =o[atTop] (fun H : ℕ => (Inverse687.full H:ℝ)) := by
  have loss := Inverse687.reduced_loss.comp_tendsto Inverse687.full_inf
  have gap : (fun H => Real.log (Inverse687.full H)-Real.log (Inverse687.weak H)) =o[atTop]
      (fun H => Real.log (Inverse687.weak H)) := by
    refine loss.trans_isBigO (Asymptotics.IsBigO.of_bound 2 ?_)
    filter_upwards [Inverse687.full_inf.eventually Inverse687.half_log] with H h
    change ‖Real.log (Inverse687.full H)‖ ≤ 2*‖Real.log (Inverse687.reduced (Inverse687.full H))‖
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_natCast_nonneg _)] using h
  have small : ∀ H, Inverse687.weak H ≤ Inverse687.full H := fun _ => Nat.div_le_self .. 
  obtain ⟨a,ha⟩ := general_inverse (cubic_of_quadratic quad) Inverse687.weak
    (Inverse687.reduced_inf.comp Inverse687.full_inf) (Eventually.of_forall small) gap
  exact ⟨a,ha,Inverse687.weak_negligible⟩

/-- Convert the native logarithmic improvement to the hypothesis of the
    inverse comparison, using the catalog's exact definition of Y. -/
theorem quadratic_of_saving (saving : ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
    (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η))) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop] (fun x : ℕ => (x:ℝ)^2) := by
  obtain ⟨η,hη,bound⟩ := saving
  apply bound.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [logs.eventually_ge_atTop 1] with x h
  change 1 ≤ Real.log (x:ℝ) at h
  have den := Real.one_le_rpow h (by linarith : 0 ≤ 2+η)
  have nn := div_nonneg (sq_nonneg (x:ℝ)) (zero_le_one.trans den)
  simpa only [Real.norm_eq_abs,abs_of_nonneg nn,abs_of_nonneg (sq_nonneg (x:ℝ)),one_mul]
    using (div_le_self (sq_nonneg (x:ℝ)) den)

end Troncature687
