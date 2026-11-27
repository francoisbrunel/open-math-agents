import SousPuissance687

/-! Consequence for Erdős's question about replacing full coverage by an
    allowed exceptional set. The hypothesis is precisely part (iii). -/
namespace Separation687
open Filter
open scoped Asymptotics

def SubpowerUpper : Prop := ∀ δ > (0:ℝ), (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
  (fun x : ℕ => (x:ℝ)^(1+δ))

theorem eventual_lower : ∀ᶠ x : ℕ in atTop, x ≤ Erdos687.Y x := by
  filter_upwards [Croissance687.superlinear.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)]
    with x h hx
  change 1 ≤ (Erdos687.Y x:ℝ)/x at h
  exact_mod_cast (one_le_div (by positivity)).mp h

theorem excess (upper : SubpowerUpper) :
    (fun x : ℕ => Real.log (Erdos687.Y x)-Real.log x) =o[atTop] (fun x : ℕ => Real.log x) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  obtain ⟨C,hC,bound⟩ := Asymptotics.isBigO_iff'.mp (upper (ε/2) (half_pos he))
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [bound,eventual_lower,eventually_ge_atTop (2:ℕ),logs.eventually_ge_atTop (2*Real.log C/ε)]
    with x h le hx hl
  have pos : (0:ℝ) < x := by positivity
  have yp : (0:ℝ) < Erdos687.Y x := by exact_mod_cast (show 0 < Erdos687.Y x by omega)
  have lx := Real.log_pos (show (1:ℝ) < x by exact_mod_cast hx)
  change ‖(Erdos687.Y x:ℝ)‖ ≤ C*‖(x:ℝ)^(1+ε/2)‖ at h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg yp.le,abs_of_nonneg (Real.rpow_nonneg pos.le _)] at h
  have lh := Real.log_le_log yp h
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos pos _).ne',Real.log_rpow pos] at lh
  have lyle := Real.log_le_log pos (show (x:ℝ) ≤ Erdos687.Y x by exact_mod_cast le)
  change 2*Real.log C/ε ≤ Real.log (x:ℝ) at hl
  have lim := (div_le_iff₀ he).mp hl
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr lyle),abs_of_nonneg lx.le]
  linarith

noncomputable def factor (x : ℕ) : ℕ := ⌊Real.log (x:ℝ)⌋₊+1
noncomputable def long (x : ℕ) : ℕ := Erdos687.Y x*factor x

theorem log_factor :
    (fun x : ℕ => Real.log (factor x)) =o[atTop] (fun x : ℕ => Real.log x) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [logs.eventually (Real.isLittleO_log_id_atTop.bound (half_pos he)),
    logs.eventually_ge_atTop (max 2 (2*Real.log 2/ε))] with x hs hl
  let L := Real.log (x:ℝ)
  change max 2 (2*Real.log 2/ε) ≤ L at hl
  have hL := (le_max_left _ _).trans hl
  have hε := (div_le_iff₀ he).mp ((le_max_right _ _).trans hl)
  have hK : 1 ≤ factor x := Nat.succ_pos _
  have hceil : (factor x:ℝ) ≤ 2*L := by
    have h := Nat.floor_le (by linarith : 0 ≤ L)
    change ((⌊L⌋₊+1:ℕ):ℝ) ≤ 2*L
    push_cast; linarith
  have up := Real.log_le_log (show (0:ℝ) < factor x by positivity) hceil
  rw [Real.log_mul (by norm_num) (by linarith)] at up
  change ‖Real.log L‖ ≤ ε/2*‖L‖ at hs
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith)),
    abs_of_nonneg (by linarith : 0 ≤ L)] at hs
  change ‖Real.log (factor x)‖ ≤ ε*‖L‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hK)),
    abs_of_nonneg (by linarith : 0 ≤ L)]
  linarith

theorem full_negligible : (fun x : ℕ => (Erdos687.Y x:ℝ)) =o[atTop] (fun x : ℕ => (long x:ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  have logs := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  filter_upwards [logs.eventually_ge_atTop (1/ε)] with x h
  have hfloor := Nat.lt_floor_add_one (Real.log (x:ℝ))
  change 1/ε ≤ Real.log (x:ℝ) at h
  have hk : 1/ε ≤ (factor x:ℝ) := by dsimp [factor]; push_cast; linarith
  have product := (div_le_iff₀ he).mp hk
  simp only [long,Nat.cast_mul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left product (Nat.cast_nonneg (α := ℝ) (Erdos687.Y x))]

/-- If the upper bound asked in part (iii) holds, an interval longer
    than Y(x) by a factor asymptotic to log x can be covered apart from
    o(H/log H) points, using precisely the same prime cutoff x. -/
theorem weak_separation (upper : SubpowerUpper) :
    ∃ a : ℕ → ℕ → ℕ, (fun x => ((Transfert687.survivors x (long x) (a x)).card:ℝ)) =o[atTop]
      (fun x => (long x:ℝ)/Real.log (long x)) ∧
      (fun x : ℕ => (Erdos687.Y x:ℝ)) =o[atTop] (fun x : ℕ => (long x:ℝ)) := by
  have large : ∀ᶠ x : ℕ in atTop, x ≤ long x := by
    filter_upwards [eventual_lower] with x le
    exact le.trans (by simpa [long] using Nat.mul_le_mul_left (Erdos687.Y x) (show 1 ≤ factor x from Nat.succ_pos _))
  have eq : (fun x : ℕ => Real.log (Erdos687.Y x)-Real.log x + Real.log (factor x)) =ᶠ[atTop]
      (fun x => Real.log (long x)-Real.log x) := by
    filter_upwards [eventual_lower,eventually_ge_atTop (2:ℕ)] with x le hx
    have y0 : (Erdos687.Y x:ℝ) ≠ 0 := by exact_mod_cast (show Erdos687.Y x ≠ 0 by omega)
    have f0 : (factor x:ℝ) ≠ 0 := by exact_mod_cast (show factor x ≠ 0 from Nat.succ_ne_zero _)
    rw [long,Nat.cast_mul,Real.log_mul y0 f0]; ring
  have scale := ((excess upper).add log_factor).congr' eq Filter.EventuallyEq.rfl
  obtain ⟨a,ha⟩ := SousPuissance687.arbitrary_length long large scale
  exact ⟨a,ha,full_negligible⟩

end Separation687
