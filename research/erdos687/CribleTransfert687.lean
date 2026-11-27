import GainVariable687
import Progressions687
import CribleOAI687
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Transfer of the OpenAI interval upper sieve to the varying cutoff. -/
namespace CribleTransfert687
open Filter Transfert687 GainVariable687 Progressions687
open scoped Asymptotics
open OAI.Erdos970.NumberTheoryLean

theorem index_upper (J z : ℕ) (b : ℕ → ℕ) (h : J ≤ z) :
    ((siftedIndices z J b).card : ℝ) ≤ 255*(1+(J:ℝ)/Real.log J) := by
  have eqn : siftedIndices z J b = LargePrimeDeletion.cutoffSurvivors J z b := by
    ext i
    simp only [siftedIndices, Finset.mem_filter, Finset.mem_range, LargePrimeDeletion.mem_cutoffSurvivors]
    constructor
    · rintro ⟨hi,avoid⟩
      exact ⟨hi,fun p hp hpz => avoid p (Nat.mem_primesLE.mpr ⟨hpz,hp⟩)⟩
    · rintro ⟨hi,avoid⟩
      exact ⟨hi,fun p hp => avoid p (Nat.mem_primesLE.mp hp).2 (Nat.mem_primesLE.mp hp).1⟩
  rw [eqn]
  exact SquarefreeHarmonic.cutoffSurvivors_le_uniform_log J z b h

/-- This separates the analytic sieve from all rounding questions. -/
theorem charge_upper {N z p : ℕ} (hp : p.Prime) (hzp : z < p) (a : ℕ → ℕ)
    (hJ : N/p+1 ≤ z) :
    (charge (survivors z N a) a p : ℝ) ≤
      255*(1+(↑(N/p+1):ℝ)/Real.log (↑(N/p+1):ℝ)) := by
  obtain ⟨b,hb⟩ := charge_le_index_sieve (N := N) hp hzp a
  exact (show (charge (survivors z N a) a p : ℝ) ≤
    ((siftedIndices z (N/p+1) b).card:ℝ) by exact_mod_cast hb).trans (index_upper _ _ _ hJ)

private theorem length_lower {x : ℕ} {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2)
    (hx : 1 ≤ x) (hL : 4 ≤ Real.log (x:ℝ))
    (hpow : 2*(Real.log (x:ℝ))^4 ≤ Real.sqrt x) (hlz : 0 < Real.log (top d x)) :
    (x:ℝ)*Real.sqrt x ≤ (length d x : ℝ) := by
  let L := Real.log (x:ℝ)
  have hL' : 4 ≤ L := hL
  have hpos : 0 < L := by linarith
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  have hM : 1 ≤ Real.sqrt x := by
    rw [Real.one_le_sqrt]; exact_mod_cast hx
  have hden : L^d ≤ L := by
    simpa using (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (show d ≤ 1 by linarith))
  have hlow : (x:ℝ)/L ≤ top d x :=
    div_le_div_of_nonneg_left hxpos.le (Real.rpow_pos_of_pos hpos _) hden
  have htop : top d x ≤ x := div_le_self hxpos.le (Real.one_le_rpow (by linarith) hd.le)
  have hlog := Real.log_le_log (div_pos hxpos (Real.rpow_pos_of_pos hpos d)) htop
  change Real.log (top d x) ≤ L at hlog
  have big : 2*(x:ℝ)*Real.sqrt x ≤ ((x:ℝ)/L)^2 / L^2 := by
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (x:ℝ)*Real.sqrt x by positivity)
    have hs := Real.sq_sqrt hxpos.le
    have hprod : 2*(x:ℝ)*Real.sqrt x*L^4 ≤ (x:ℝ)^2 := by
      calc
        _ = ((x:ℝ)*Real.sqrt x)*(2*L^4) := by ring
        _ ≤ ((x:ℝ)*Real.sqrt x)*Real.sqrt x := hp
        _ = (x:ℝ) * (Real.sqrt x)^2 := by ring
        _ = (x:ℝ)^2 := by rw [hs]; ring
    calc
      _ ≤ (x:ℝ)^2/L^4 := (le_div_iff₀ (by positivity)).2 hprod
      _ = _ := by field_simp
  have cmp : ((x:ℝ)/L)^2/L^2 ≤ (top d x)^2/(Real.log (top d x))^2 := by gcongr
  have floorlt := Nat.lt_floor_add_one ((top d x)^2/(Real.log (top d x))^2)
  change _ < (length d x : ℝ)+1 at floorlt
  have h1 : (1:ℝ) ≤ (x:ℝ)*Real.sqrt x :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hx) hM
  linarith [big.trans cmp]

theorem uniform_progression {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    progressionBound 1275 d := by
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have small := (isLittleO_log_rpow_atTop (show 0 < (1/10:ℝ) by norm_num)).bound
    (show (0:ℝ) < 1 by norm_num)
  unfold progressionBound
  filter_upwards [hinf.eventually_ge_atTop 4, eventually_ge_atTop (1:ℕ),
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop).eventually small]
    with x hL hx hslow
  let L := Real.log (x:ℝ)
  let z := top d x
  let N := length d x
  have hL' : 4 ≤ L := hL
  have hl : 0 < L := by linarith
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  have hslow' : L ≤ (x:ℝ)^(1/10:ℝ) := by
    change ‖L‖ ≤ 1 * ‖(x:ℝ)^(1/10:ℝ)‖ at hslow
    simpa only [Real.norm_eq_abs, abs_of_nonneg hl.le,
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _), one_mul] using hslow
  have hfifth : L^5 ≤ Real.sqrt x := by
    calc
      _ ≤ ((x:ℝ)^(1/10:ℝ))^5 := pow_le_pow_left₀ hl.le hslow' _
      _ = Real.sqrt x := by
        rw [Real.sqrt_eq_rpow, show (1/2:ℝ) = (1/10:ℝ)*5 by norm_num, Real.rpow_mul hxpos.le]
        norm_num
  have hpow : 2*L^4 ≤ Real.sqrt x := by
    calc
      _ ≤ L*L^4 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = L^5 := by ring
      _ ≤ _ := hfifth
  have hML : L ≤ Real.sqrt x := by
    have hp : 1 ≤ L^3 := one_le_pow₀ (by linarith)
    have hL4 : L ≤ L^4 := by nlinarith [mul_le_mul_of_nonneg_left hp hl.le]
    linarith [show 0 ≤ L^4 by positivity]
  have hpden := Real.rpow_pos_of_pos hl d
  have hlog : Real.log z = L-d*Real.log L := by
    change Real.log ((x:ℝ)/L^d) = _
    rw [Real.log_div hxpos.ne' hpden.ne', Real.log_rpow hl]
  have hlower : L/2 ≤ Real.log z := by
    rw [hlog]
    linarith [mul_le_mul_of_nonneg_right hh (Real.log_nonneg (show 1 ≤ L by linarith)),
      Real.log_le_sub_one_of_pos hl]
  have hzlog : 2 ≤ Real.log z := by linarith
  have hzpos : 0 < z := div_pos hxpos hpden
  have hz : 2 ≤ z := by linarith [Real.log_le_sub_one_of_pos hzpos]
  have hN : (x:ℝ)*Real.sqrt x ≤ (N:ℝ) := length_lower hd hh hx hL hpow (by linarith)
  have hNup : (N:ℝ) ≤ z^2 / (Real.log z)^2 := Nat.floor_le (by positivity)
  intro a p pmem
  obtain ⟨hpx,hout⟩ := Finset.mem_sdiff.mp pmem
  obtain ⟨px,prime⟩ := Nat.mem_primesLE.mp hpx
  have hzp : ⌊z⌋₊ < p := by
    by_contra! h
    exact hout (Nat.mem_primesLE.mpr ⟨h,prime⟩)
  have hzpr : z ≤ (p:ℝ) := (Nat.lt_floor_add_one z).le.trans
    (by exact_mod_cast (show ⌊z⌋₊+1 ≤ p by omega))
  have hpr : (0:ℝ) < p := by exact_mod_cast prime.pos
  let M := (N:ℝ)/p
  let J := N/p+1
  have hMJ : M ≤ (J:ℝ) := (div_le_iff₀ hpr).2 (by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul prime.pos).1 (Nat.lt_succ_self (N/p))).le)
  have hJM : (J:ℝ) ≤ M+1 := by
    dsimp [J,M]; push_cast
    exact add_le_add Nat.cast_div_le (le_refl (1:ℝ))
  have hMlow : Real.sqrt x ≤ M := (le_div_iff₀ hpr).2 <| calc
    _ ≤ Real.sqrt x*(x:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast px) (by positivity)
    _ = _ := mul_comm _ _
    _ ≤ _ := hN
  have hMup : M ≤ z/2 := (div_le_iff₀ hpr).2 <| calc
    (N:ℝ) ≤ z^2/(Real.log z)^2 := hNup
    _ ≤ z^2/(2:ℝ)^2 := by gcongr
    _ ≤ (z/2)*p := by nlinarith [mul_le_mul_of_nonneg_left hzpr hzpos.le, sq_nonneg z]
  have hJz : J ≤ ⌊z⌋₊ := (Nat.le_floor_iff hzpos.le).2 (by linarith)
  have hlogJ : L/2 ≤ Real.log (J:ℝ) := by
    simpa only [Real.log_sqrt hxpos.le] using Real.log_le_log (Real.sqrt_pos.2 hxpos) (hMlow.trans hMJ)
  have hM1 : 1 ≤ M := by linarith
  have hquot : (J:ℝ)/Real.log J ≤ 4*M/L := calc
    _ ≤ (2*M)/(L/2) := by gcongr <;> linarith
    _ = _ := by ring
  have hunit : 1 ≤ M/L := (le_div_iff₀ hl).2 (by linarith)
  have hquot' : (J:ℝ)/Real.log J ≤ 4*(M/L) := by simpa only [mul_div_assoc] using hquot
  have found := charge_upper (N := N) prime hzp a hJz
  change (charge (survivors ⌊z⌋₊ N a) a p:ℝ) ≤ 255*(1+(J:ℝ)/Real.log (J:ℝ)) at found
  calc
    _ ≤ _ := found
    _ ≤ 255*((M/L)+4*(M/L)) := mul_le_mul_of_nonneg_left (add_le_add hunit hquot') (by norm_num)
    _ = 1275*(M/L) := by ring
    _ = _ := by unfold classUnit; dsimp [M,N,L]; ring

/-- Only the uniform lower-sieve stock estimate remains. -/
theorem gain_from_stock
    (stock : ∃ c : ℝ, 0 < c ∧ ∀ d : ℝ, 0 < d → d ≤ 1/2 → stockBound c d) :
    ∃ η : ℝ, 0 < η ∧ (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^2/(Real.log x)^(2+η)) :=
  exists_log_saving stock ⟨1275, by norm_num, fun _ hd hh => uniform_progression hd hh⟩

end CribleTransfert687
