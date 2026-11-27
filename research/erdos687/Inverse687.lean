import Separation687

/-! Erdős's inverse formulation: the smallest prime cutoff admitting
    a complete cover of an interval of given length. -/
namespace Inverse687
open Filter Separation687
open scoped Asymptotics

theorem Y_mono : Monotone Erdos687.Y := by
  intro z x hz
  obtain ⟨a,ha⟩ := Extension687.optimal_cover z
  apply Transfert687.le_Y_of_covered
  refine ⟨a,fun n hn => ?_⟩
  obtain ⟨p,le,pr,hit⟩ := ha n hn
  exact ⟨p,le.trans hz,pr,hit⟩

noncomputable def full (H : ℕ) : ℕ := sInf {x : ℕ | H ≤ Erdos687.Y x}

theorem full_spec (H : ℕ) : H ≤ Erdos687.Y (full H) := by
  change sInf {x : ℕ | H ≤ Erdos687.Y x} ∈ {x : ℕ | H ≤ Erdos687.Y x}
  apply Nat.sInf_mem
  obtain ⟨x,hx,le⟩ := (Filter.eventually_ge_atTop H |>.and eventual_lower).exists
  exact ⟨x,hx.trans le⟩

theorem full_le_iff {H x : ℕ} : full H ≤ x ↔ H ≤ Erdos687.Y x :=
  ⟨fun le => (full_spec H).trans (Y_mono le),fun le => Nat.sInf_le le⟩

theorem full_inf : Tendsto full atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (Erdos687.Y k+1)] with H h
  by_contra! no
  exact (by omega : ¬H ≤ Erdos687.Y k) (full_le_iff.mp no.le)

private theorem full_small : ∀ᶠ H : ℕ in atTop, full H ≤ H :=
  eventual_lower.mono (fun _ h => full_le_iff.mpr h)

noncomputable def reduced (x : ℕ) : ℕ := x / factor x

private theorem bounds : ∀ᶠ x : ℕ in atTop,
    1 ≤ reduced x ∧ reduced x ≤ x ∧ x ≤ 2*reduced x*factor x := by
  filter_upwards [eventually_ge_atTop (2:ℕ)] with x hx
  have xp : (0:ℝ) < x := by positivity
  have log0 := Real.log_nonneg (show (1:ℝ) ≤ x by exact_mod_cast (show 1 ≤ x by omega))
  have kx : factor x ≤ x := by
    have h := Nat.floor_le log0
    have le := Real.log_le_sub_one_of_pos xp
    exact_mod_cast (show (factor x:ℝ) ≤ x by dsimp [factor]; push_cast; linarith)
  have kp : 0 < factor x := Nat.succ_pos _
  have rp : 1 ≤ reduced x := (Nat.div_pos kx kp)
  have cover := (Nat.div_lt_iff_lt_mul kp).mp (Nat.lt_succ_self (x/factor x))
  change x < (reduced x+1)*factor x at cover
  exact ⟨rp,Nat.div_le_self ..,cover.le.trans (Nat.mul_le_mul_right _ (by omega))⟩

private theorem logs_inf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem reduced_loss :
    (fun x : ℕ => Real.log x-Real.log (reduced x)) =o[atTop] (fun x : ℕ => Real.log x) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  filter_upwards [bounds,eventually_ge_atTop (2:ℕ),log_factor.bound (half_pos he),
    logs_inf.eventually_ge_atTop (2*Real.log 2/ε)] with x hb hx hfactor hlog
  obtain ⟨rp,rx,cover⟩ := hb
  have xp : (0:ℝ) < x := by positivity
  have rpos : (0:ℝ) < reduced x := by exact_mod_cast rp
  have kpos : 0 < factor x := Nat.succ_pos _
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast hx)
  have le := Real.log_le_log rpos (show (reduced x:ℝ) ≤ x by exact_mod_cast rx)
  have top := Real.log_le_log xp (show (x:ℝ) ≤ 2*reduced x*factor x by exact_mod_cast cover)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) rpos.ne'] at top
  change 2*Real.log 2/ε ≤ Real.log (x:ℝ) at hlog
  have lim := (div_le_iff₀ he).mp hlog
  change ‖Real.log (factor x)‖ ≤ ε/2*‖Real.log (x:ℝ)‖ at hfactor
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast kpos)),
    abs_of_nonneg lx.le] at hfactor
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr le),abs_of_nonneg lx.le]
  linarith

private theorem half_log : ∀ᶠ x : ℕ in atTop, Real.log (x:ℝ) ≤ 2*Real.log (reduced x) := by
  filter_upwards [reduced_loss.bound (by norm_num : (0:ℝ)<1/2),bounds,eventually_ge_atTop (2:ℕ)]
    with x h hb hx
  have le := Real.log_le_log (by exact_mod_cast hb.1 : (0:ℝ)<reduced x)
    (show (reduced x:ℝ) ≤ x by exact_mod_cast hb.2.1)
  have lx := Real.log_pos (show (1:ℝ)<x by exact_mod_cast hx)
  change ‖Real.log x-Real.log (reduced x)‖ ≤ 1/2*‖Real.log (x:ℝ)‖ at h
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr le),abs_of_nonneg lx.le] at h
  linarith

theorem reduced_inf : Tendsto reduced atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [half_log,bounds,logs_inf.eventually_ge_atTop (2*Real.log (b+1:ℕ))] with x h hb hl
  have bp : (0:ℝ) < (b+1:ℕ) := by positivity
  change 2*Real.log (b+1:ℕ) ≤ Real.log (x:ℝ) at hl
  have le := (Real.log_le_log_iff bp (by exact_mod_cast hb.1 : (0:ℝ)<reduced x)).mp (by linarith)
  exact (Nat.le_succ b).trans (by exact_mod_cast le)

theorem reduced_negligible :
    (fun x : ℕ => (reduced x:ℝ)) =o[atTop] (fun x : ℕ => (x:ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε he
  filter_upwards [logs_inf.eventually_ge_atTop (1/ε)] with x hl
  change 1/ε ≤ Real.log (x:ℝ) at hl
  have f := Nat.lt_floor_add_one (Real.log (x:ℝ))
  have hk : 1/ε ≤ (factor x:ℝ) := by dsimp [factor]; push_cast; linarith
  have scale := (div_le_iff₀ he).mp hk
  have cap : (reduced x:ℝ)*factor x ≤ x := by exact_mod_cast Nat.div_mul_le_self x (factor x)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_right scale (Nat.cast_nonneg (α := ℝ) (reduced x)),
    mul_le_mul_of_nonneg_left cap he.le]

/-- The cutoff used for almost-coverage, as a function of the interval
    length. It is asymptotic to full H / log (full H). -/
noncomputable def weak (H : ℕ) : ℕ := reduced (full H)

theorem weak_negligible :
    (fun H : ℕ => (weak H:ℝ)) =o[atTop] (fun H : ℕ => (full H:ℝ)) :=
  reduced_negligible.comp_tendsto full_inf

/-- If part (iii) holds, the same explicit, asymptotically smaller
    cutoff almost-covers every sufficiently large interval length with
    o(H/log H) exceptions. Full coverage requires precisely full H. -/
theorem inverse_separation (upper : SubpowerUpper) :
    ∃ a : ℕ → ℕ → ℕ, (fun H : ℕ => ((Transfert687.survivors (weak H) H (a H)).card:ℝ))
      =o[atTop] (fun H : ℕ => (H:ℝ)/Real.log H) ∧
      (fun H : ℕ => (weak H:ℝ)) =o[atTop] (fun H : ℕ => (full H:ℝ)) := by
  have winf : Tendsto weak atTop atTop := reduced_inf.comp full_inf
  have le : ∀ᶠ H : ℕ in atTop, weak H ≤ H := by
    filter_upwards [full_inf.eventually bounds,full_small] with H h small
    exact h.2.1.trans small
  have scale : (fun H : ℕ => Real.log H-Real.log (weak H)) =o[atTop]
      (fun H : ℕ => Real.log (weak H)) := by
    apply Asymptotics.isLittleO_iff.mpr
    intro ε he
    have quarter : 0 < ε/4 := by positivity
    filter_upwards [full_inf.eventually ((excess upper).bound quarter),
      full_inf.eventually (reduced_loss.bound quarter),full_inf.eventually half_log,
      full_inf.eventually bounds,full_small,full_inf.eventually_ge_atTop 2,
      winf.eventually_ge_atTop 2] with H hs hr hf hb fh f2 w2
    let f := full H
    let w := weak H
    have wf : w ≤ f := hb.2.1
    have wh : w ≤ H := wf.trans fh
    have xy := full_spec H
    have fp : (0:ℝ) < f := by exact_mod_cast (show 0 < full H by omega)
    have wp : (0:ℝ) < w := by exact_mod_cast (show 0 < weak H by omega)
    have hp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
    have lf := Real.log_pos (show (1:ℝ)<f by exact_mod_cast f2)
    have lw := Real.log_pos (show (1:ℝ)<w by exact_mod_cast w2)
    have wy := Real.log_le_log wp (show (w:ℝ) ≤ H by exact_mod_cast wh)
    have fw := Real.log_le_log wp (show (w:ℝ) ≤ f by exact_mod_cast wf)
    have hy := Real.log_le_log hp (show (H:ℝ) ≤ Erdos687.Y f by exact_mod_cast xy)
    have fy := Real.log_le_log fp (show (f:ℝ) ≤ Erdos687.Y f by exact_mod_cast fh.trans xy)
    change ‖Real.log (Erdos687.Y f)-Real.log f‖ ≤ ε/4*‖Real.log (f:ℝ)‖ at hs
    change ‖Real.log f-Real.log w‖ ≤ ε/4*‖Real.log (f:ℝ)‖ at hr
    change Real.log (f:ℝ) ≤ 2*Real.log w at hf
    change ‖Real.log H-Real.log w‖ ≤ ε*‖Real.log (w:ℝ)‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr wy),abs_of_nonneg lw.le]
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr fy),abs_of_nonneg lf.le] at hs
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr fw),abs_of_nonneg lf.le] at hr
    nlinarith [mul_le_mul_of_nonneg_left hf he.le]
  obtain ⟨a,ha⟩ := SousPuissance687.arbitrary_length_along weak id winf le scale
  exact ⟨a,ha,weak_negligible⟩

end Inverse687
