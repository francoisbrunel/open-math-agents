import Sauts687
import BorneRankin687
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! Prime jumps on the scale supplied by the classical Rankin construction. -/
namespace SautsRankin687
open Filter Sauts687 BorneRankin687
open scoped Asymptotics

noncomputable def scale (x : ℕ) : ℝ := (Real.log x/Real.log (Real.log x))^2

private theorem grows : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem interval (C : ℝ) (nn : 0≤C) : ∀ᶠ x : ℕ in atTop, ∀ z≤x,
    2*Erdos687.Y z ≤ Erdos687.Y x →
    ∃ p, z<p ∧ p≤x ∧ p.Prime ∧ C*scale x < jump p := by
  obtain ⟨K,hK,hb⟩ := Asymptotics.isBigO_iff'.mp rankin_lower
  filter_upwards [hb,(Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp grows)).eventually_gt_atTop (32*K*C+1),
    (Real.tendsto_log_atTop.comp grows).eventually_ge_atTop 2,grows.eventually_ge_atTop 2,
    eventually_ge_atTop (2:ℕ)] with x bound top big lbound hx
  let L := Real.log (x:ℝ)
  let l := Real.log L
  have xp : (0:ℝ)<x := by exact_mod_cast (by omega : 0<x)
  have lp : 0<L := by change 2≤L at lbound; linarith
  have ll : 0<l := by change 2≤l at big; linarith
  have lt3 : 32*K*C+1<Real.log l := top
  have pos3 : 0<Real.log l := by nlinarith [mul_nonneg hK.le nn]
  have b : lowerScale x ≤ K*(Erdos687.Y x:ℝ) := by
    have sn : 0≤lowerScale x := by
      change 0≤(x:ℝ)*L*Real.log l/l^2; positivity
    simpa only [Real.norm_eq_abs,abs_of_nonneg sn,abs_of_nonneg (show (0:ℝ)≤Erdos687.Y x by positivity)] using bound
  have sp : 0<scale x := by change 0<(L/l)^2; positivity
  have exceeds : C*scale x < (Erdos687.Y x:ℝ)*L/(32*x) := calc
    _ < (Real.log l/(32*K))*scale x := by
      apply mul_lt_mul_of_pos_right _ sp
      apply (lt_div_iff₀ (by positivity)).mpr; nlinarith
    _ = (lowerScale x*L/(32*x))/K := by
      change _*(L/l)^2=(((x:ℝ)*L*Real.log l/l^2)*L/(32*x))/K
      field_simp <;> ring
    _ ≤ (K*(Erdos687.Y x:ℝ)*L/(32*x))/K := by gcongr
    _ = _ := by field_simp
  intro z zx cap
  apply large_jump hx zx (mul_nonneg nn sp.le)
  have ypos : (0:ℝ)<Erdos687.Y x := by
    by_contra! bad
    have y0 := le_antisymm bad (Nat.cast_nonneg _)
    rw [y0,zero_mul,zero_div] at exceeds
    exact (not_lt_of_ge (mul_nonneg nn sp.le)) exceeds
  have converted : 2*(Erdos687.Y z:ℝ) ≤ Erdos687.Y x := by exact_mod_cast cap
  have h := mul_lt_mul_of_pos_left exceeds (show 0<8*(x:ℝ)/L by positivity)
  have eq : (8*(x:ℝ)/L)*((Erdos687.Y x:ℝ)*L/(32*x)) = Erdos687.Y x/4 := by field_simp <;> ring
  rw [eq] at h
  change (Erdos687.Y z:ℝ)+8*x/L*(C*scale x) < _
  linarith

private theorem scale_mono {p x : ℕ} (large : Real.exp 1≤Real.log (p:ℝ)) (pp : 0<p)
    (px : p≤x) : scale p ≤ scale x := by
  have logs := Real.log_le_log (show (0:ℝ)<p by exact_mod_cast pp) (show (p:ℝ)≤x by exact_mod_cast px)
  have p1 : 1<Real.log (p:ℝ) := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le large
  have x1 := p1.trans_le logs
  have cmp := Real.log_div_self_antitoneOn large (large.trans logs) logs
  have a := (div_le_div_iff₀ (by linarith : 0<Real.log (x:ℝ)) (by linarith : 0<Real.log (p:ℝ))).mp cmp
  have b : Real.log p/Real.log (Real.log p) ≤ Real.log x/Real.log (Real.log x) :=
    (div_le_div_iff₀ (Real.log_pos p1) (Real.log_pos x1)).mpr (by linarith)
  exact pow_le_pow_left₀ (div_nonneg (by linarith) (Real.log_pos p1).le) b 2

theorem arbitrarily_large (C : ℝ) (nn : 0≤C) (z : ℕ) :
    ∃ p, z<p ∧ p.Prime ∧ C*scale p < jump p := by
  obtain ⟨z',large,zle⟩ := ((grows.eventually_ge_atTop (Real.exp 1)).and (eventually_ge_atTop z)).exists
  have yl : ∀ᶠ x : ℕ in atTop, 2*Erdos687.Y z'≤Erdos687.Y x := by
    filter_upwards [Croissance687.superlinear.eventually_gt_atTop 1,
      eventually_ge_atTop (2*Erdos687.Y z'),eventually_ge_atTop (1:ℕ)] with x high hx pos
    change 1 < (Erdos687.Y x:ℝ)/x at high
    have more := (lt_div_iff₀ (by exact_mod_cast (by omega : 0<x) : (0:ℝ)<x)).mp high
    have le : x≤Erdos687.Y x := by exact_mod_cast (show (x:ℝ)≤Erdos687.Y x by linarith)
    exact hx.trans le
  obtain ⟨x,h,zx,cap⟩ := ((interval C nn).and ((eventually_ge_atTop z').and yl)).exists
  obtain ⟨p,pz,px,pr,big⟩ := h z' zx cap
  have zp : 0<z' := by
    by_contra! e; have : z'=0 := by omega
    simpa [this,not_le_of_gt (Real.exp_pos _)] using large
  have above := large.trans (Real.log_le_log (by exact_mod_cast zp) (show (z':ℝ)≤p by exact_mod_cast pz.le))
  exact ⟨p,zle.trans_lt pz,pr,(mul_le_mul_of_nonneg_left (scale_mono above pr.pos px) nn).trans_lt big⟩

end SautsRankin687

#print axioms SautsRankin687.arbitrarily_large
