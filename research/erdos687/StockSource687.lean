import CribleTransfert687
import Mertens687
import InterfaceSource687

/-! Normalize Theorem 1.2 of OpenAI's Jacobsthal manuscript, including
the two interval conventions, the Euler product and the uniform constants. -/
namespace StockSource687
open Filter GainVariable687 Transfert687
open scoped Asymptotics BigOperators
open OAI.Erdos970.NumberTheoryLean

noncomputable def width (z : ℝ) : ℝ := Real.log z / (Real.log (Real.log z))^2
noncomputable def height (z : ℝ) : ℕ := ⌊z^2 / (Real.log z)^2⌋₊
noncomputable def scale (z : ℝ) : ℝ := Real.log z / Real.log (width z)

/-- The published quantitative input, with the authors' zero-based
cutoff-survivor set. The Euler product runs through floor(width z). -/
def sourceStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
    c * ((height z : ℝ) * OMA_M3.Qm ⌊width z⌋₊ / (scale z)^2) ≤
      ((LargePrimeDeletion.cutoffSurvivors (height z) ⌊z⌋₊ a).card : ℝ)

private theorem shift_survivors (N z : ℕ) (a : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, (LargePrimeDeletion.cutoffSurvivors N z b).card ≤ (survivors z N a).card := by
  let b (p : ℕ) := a p + p - 1
  refine ⟨b, Finset.card_le_card_of_injOn (fun i : ℕ => i+1) ?_ ?_⟩
  · intro i hi
    obtain ⟨hiN,avoid⟩ := LargePrimeDeletion.mem_cutoffSurvivors.mp hi
    change i+1 ∈ survivors z N a
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.succ_pos i,hiN⟩,?_⟩
    intro p hp he
    obtain ⟨hpz,prime⟩ := Nat.mem_primesLE.mp hp
    have pos := prime.pos
    have translate : (b p+1) ≡ a p [MOD p] := by
      have eqn : b p+1 = a p+p := by dsimp [b]; omega
      rw [eqn]
      change (a p+p)%p = a p%p
      simp
    exact avoid p prime hpz (Nat.ModEq.add_right_cancel' 1 ((show i+1 ≡ a p [MOD p] from he).trans translate.symm))
  · intro i _ j _ he
    exact Nat.add_right_cancel he

private theorem width_eventually :
    ∀ᶠ z : ℝ in atTop, 3 ≤ ⌊width z⌋₊ ∧ Real.log (Real.log z)/2 ≤ Real.log (width z) := by
  have hu : Tendsto (fun z : ℝ => Real.log (Real.log z)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have small := Real.isLittleO_log_id_atTop.bound (show 0 < (1/4:ℝ) by norm_num)
  filter_upwards [hu.eventually_ge_atTop 8, hu.eventually small,
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with z hlarge hs ht
  let t := Real.log z
  let u := Real.log t
  change 8 ≤ u at hlarge
  change 2 ≤ t at ht
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hb : Real.log u ≤ (1/4:ℝ)*u := by
    change ‖Real.log u‖ ≤ (1/4:ℝ)*‖u‖ at hs
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlogu,abs_of_nonneg hu0.le] using hs
  have hw : Real.log (width z) = u - 2*Real.log u := by
    change Real.log (t/u^2) = _
    rw [Real.log_div ht0.ne' (pow_pos hu0 _).ne',Real.log_pow]
    rfl
  have wp : 0 < width z := div_pos ht0 (pow_pos hu0 _)
  have h3 : (3:ℝ) ≤ width z := by linarith [Real.log_le_sub_one_of_pos wp]
  exact ⟨(Nat.le_floor_iff wp.le).2 (by simpa using h3),by change u/2 ≤ _; linarith⟩

/-- A real-cutoff estimate, before composing with any exponent d. -/
theorem normalize_source (h : sourceStatement) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ in atTop, ∀ a : ℕ → ℕ,
      c * ((height z:ℝ) * Real.log (Real.log z) / (Real.log z)^2) ≤
        ((survivors ⌊z⌋₊ (height z) a).card:ℝ) := by
  obtain ⟨c,hc,hs⟩ := h
  refine ⟨c/6,by positivity,?_⟩
  filter_upwards [hs,width_eventually,Real.tendsto_log_atTop.eventually_ge_atTop 2] with z hz hw ht
  intro a
  let w := width z
  have hw' : (3:ℝ) ≤ (⌊w⌋₊:ℝ) := by exact_mod_cast hw.1
  have wp : 0 ≤ w := (Nat.cast_nonneg ⌊w⌋₊).trans (Nat.floor_le (by
    change 0 ≤ Real.log z / _; exact div_nonneg (by linarith) (sq_nonneg _)))
  have floorle : (⌊w⌋₊:ℝ) ≤ w := Nat.floor_le wp
  have hlogf : 0 < Real.log (⌊w⌋₊:ℝ) := Real.log_pos (by linarith)
  have ht' : 0 < Real.log z := by linarith
  have hfw := Real.log_le_log (show (0:ℝ) < ⌊w⌋₊ by linarith) floorle
  have hlw : 0 < Real.log w := hlogf.trans_le hfw
  have euler : 1/(3*Real.log w) ≤ OMA_M3.Qm ⌊w⌋₊ :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)).trans (OMA_M3.main _ hw.1)
  obtain ⟨b,shift⟩ := shift_survivors (height z) ⌊z⌋₊ a
  have en : (0:ℝ) ≤ height z := by positivity
  have positive : 0 ≤ Real.log (Real.log z) := Real.log_nonneg (by linarith)
  have lower : (height z:ℝ) * Real.log (Real.log z) / (6 * (Real.log z)^2) ≤
        (height z:ℝ) * OMA_M3.Qm ⌊w⌋₊ / (scale z)^2 := calc
    _ ≤ (height z:ℝ) * (2*Real.log w) / (6*(Real.log z)^2) := by
      gcongr; linarith [hw.2]
    _ = (height z:ℝ) * (1/(3*Real.log w)) / (scale z)^2 := by
      change _ = _ / (Real.log z / Real.log w)^2
      field_simp
      ring
    _ ≤ _ := by gcongr
  calc
    _ = c*((height z:ℝ)*Real.log (Real.log z)/(6*(Real.log z)^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lower hc.le
    _ ≤ _ := hz b
    _ ≤ _ := by exact_mod_cast shift

private theorem cutoff_properties {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, 0 < Real.log (top d x) ∧ Real.log (top d x) ≤ Real.log x ∧
      Real.log x/2 ≤ Real.log (top d x) ∧ Real.log (Real.log x)/2 ≤ Real.log (Real.log (top d x)) := by
  have ht : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 4, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 4,
    eventually_ge_atTop (1:ℕ)] with x hL hLL hx
  let L := Real.log (x:ℝ)
  change 4 ≤ L at hL
  change 4 ≤ Real.log L at hLL
  have hl : 0 < L := by linarith
  have hp : 0 < (x:ℝ) := by exact_mod_cast hx
  have he : Real.log (top d x) = L-d*Real.log L := by
    rw [top,Real.log_div hp.ne' (Real.rpow_pos_of_pos hl d).ne', Real.log_rpow hl]
  have hlo : L/2 ≤ Real.log (top d x) := by
    rw [he]
    linarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ Real.log L by linarith),Real.log_le_sub_one_of_pos hl]
  have hhi : Real.log (top d x) ≤ L := by rw [he]; nlinarith [mul_nonneg hd.le (show 0 ≤ Real.log L by linarith)]
  have loglo := Real.log_le_log (show 0 < L/2 by positivity) hlo
  rw [Real.log_div hl.ne' (by norm_num)] at loglo
  exact ⟨by linarith,hhi,hlo,by change Real.log L/2 ≤ _; linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]⟩

theorem stock_of_published (h : sourceStatement) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → stockBound c d := by
  obtain ⟨c,hc,hs⟩ := normalize_source h
  refine ⟨c/2,by positivity,?_⟩
  intro d hd hh
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcut := cutoff_properties hd hh
  have htop : Tendsto (top d) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hcut,hinf.eventually_ge_atTop (2*b),eventually_ge_atTop (1:ℕ),
      hinf.eventually_ge_atTop 2] with x h hL hx hpos
    have hp : 0 < top d x := div_pos (by exact_mod_cast hx) (Real.rpow_pos_of_pos (by linarith : 0 < Real.log (x:ℝ)) _)
    change 2*b ≤ Real.log (x:ℝ) at hL
    linarith [h.2.2.1, Real.log_le_sub_one_of_pos hp]
  unfold stockBound
  filter_upwards [htop.eventually hs,hcut,hinf.eventually_ge_atTop 2] with x h hcmp hL
  intro a
  let L := Real.log (x:ℝ)
  let t := Real.log (top d x)
  let N := length d x
  have hl : 0 < L := by change 2 ≤ L at hL; linarith
  have hll : 0 ≤ Real.log L := Real.log_nonneg (by change 2 ≤ L at hL; linarith)
  have ht : 0 < t := hcmp.1
  have htl : t ≤ L := hcmp.2.1
  have hllt : Real.log L/2 ≤ Real.log t := hcmp.2.2.2
  have hlogt : 0 ≤ Real.log t := by linarith
  have hstock := h a
  change c*((N:ℝ)*Real.log t/t^2) ≤ _ at hstock
  calc
    _ = c*((N:ℝ)*(Real.log L/2)/L^2) := by unfold stockUnit classUnit; dsimp [N,L]; ring
    _ ≤ c*((N:ℝ)*Real.log t/t^2) := by gcongr
    _ ≤ _ := hstock

/-- The complete transfer from the quantitative source bound to the upper
bound on the official Y. The existence of a matching lower bound is separate. -/
theorem gain_of_published (h : sourceStatement) :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) :=
  CribleTransfert687.gain_from_stock (stock_of_published h)

theorem source_of_interface (h : InterfaceSource687.statement) : sourceStatement := by
  have agree (N z : ℕ) (a : ℕ → ℕ) : InterfaceSource687.remaining N z a =
      LargePrimeDeletion.cutoffSurvivors N z a := by
    classical
    ext i
    simp only [InterfaceSource687.remaining,InterfaceSource687.primes,
      LargePrimeDeletion.cutoffSurvivors,LargePrimeDeletion.cutoffPrimes,
      SievePartition.survivors,SievePartition.residueBad,Finset.mem_filter]
  simpa only [sourceStatement,height,width,scale,OMA_M3.Qm,
    InterfaceSource687.statement,InterfaceSource687.height,InterfaceSource687.width,
    InterfaceSource687.scale,InterfaceSource687.product,InterfaceSource687.primes,agree] using h

theorem gain_of_interface (h : InterfaceSource687.statement) :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) :=
  gain_of_published (source_of_interface h)

end StockSource687
