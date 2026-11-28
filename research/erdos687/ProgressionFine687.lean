import CribleFin687
import CribleTransfert687

/-! A uniform 9/4 progression constant at logarithmic cutoffs. -/
namespace ProgressionFine687
open Filter Transfert687 GainVariable687 Progressions687 CribleTransfert687
open scoped Asymptotics
open OAI.Erdos970.NumberTheoryLean

private theorem length_lower {x : ℕ} {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2)
    (hx : 1 ≤ x) (hL : 4 ≤ Real.log (x:ℝ))
    (hpow : 2*(Real.log (x:ℝ))^4 ≤ (x:ℝ)^(1/100:ℝ)) (hlz : 0 < Real.log (top d x)) :
    (x:ℝ)*(x:ℝ)^(99/100:ℝ) ≤ (length d x : ℝ) := by
  let L := Real.log (x:ℝ)
  have hL' : 4 ≤ L := hL
  have hpos : 0 < L := by linarith
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  have hM : 1 ≤ (x:ℝ)^(99/100:ℝ) := by
    exact Real.one_le_rpow (by exact_mod_cast hx) (by norm_num)
  have hden : L^d ≤ L := by
    simpa using (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (show d ≤ 1 by linarith))
  have hlow : (x:ℝ)/L ≤ top d x :=
    div_le_div_of_nonneg_left hxpos.le (Real.rpow_pos_of_pos hpos _) hden
  have htop : top d x ≤ x := div_le_self hxpos.le (Real.one_le_rpow (by linarith) hd.le)
  have hlog := Real.log_le_log (div_pos hxpos (Real.rpow_pos_of_pos hpos d)) htop
  change Real.log (top d x) ≤ L at hlog
  have big : 2*(x:ℝ)*(x:ℝ)^(99/100:ℝ) ≤ ((x:ℝ)/L)^2 / L^2 := by
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (x:ℝ)*(x:ℝ)^(99/100:ℝ) by positivity)
    have hs : (x:ℝ)^(99/100:ℝ)*(x:ℝ)^(1/100:ℝ) = x := by rw [← Real.rpow_add hxpos]; norm_num
    have hprod : 2*(x:ℝ)*(x:ℝ)^(99/100:ℝ)*L^4 ≤ (x:ℝ)^2 := by
      calc
        _ = ((x:ℝ)*(x:ℝ)^(99/100:ℝ))*(2*L^4) := by ring
        _ ≤ ((x:ℝ)*(x:ℝ)^(99/100:ℝ))*(x:ℝ)^(1/100:ℝ) := hp
        _ = (x:ℝ) * ((x:ℝ)^(99/100:ℝ)*(x:ℝ)^(1/100:ℝ)) := by ring
        _ = (x:ℝ)^2 := by rw [hs]; ring
    calc
      _ ≤ (x:ℝ)^2/L^4 := (le_div_iff₀ (by positivity)).2 hprod
      _ = _ := by field_simp
  have cmp : ((x:ℝ)/L)^2/L^2 ≤ (top d x)^2/(Real.log (top d x))^2 := by gcongr
  have floorlt := Nat.lt_floor_add_one ((top d x)^2/(Real.log (top d x))^2)
  change _ < (length d x : ℝ)+1 at floorlt
  have h1 : (1:ℝ) ≤ (x:ℝ)*(x:ℝ)^(99/100:ℝ) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hx) hM
  linarith [big.trans cmp]

/-- A class modulo q can be estimated using any smaller reference modulus p
    between the real cutoff and x. This includes primes q above x. -/
theorem progression_at_reference {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    ∀ᶠ x : ℕ in atTop, ∀ (a : ℕ → ℕ) (p q : ℕ), p ≤ x → top d x ≤ (p:ℝ) →
      p ≤ q → q.Prime → ⌊top d x⌋₊ < q →
      (charge (survivors ⌊top d x⌋₊ (length d x) a) a q : ℝ) ≤ (9/4)*(classUnit d x/p) := by
  have hinf : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have inf := (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  have slow := ((isLittleO_log_rpow_rpow_atTop 4 (by norm_num : 0 < (1/100:ℝ))).comp_tendsto inf).bound
    (by norm_num : 0 < (1/2:ℝ))
  obtain ⟨Jmin,hfilter⟩ := eventually_atTop.mp (CribleFin687.asymptotic_interval (1/10) (by norm_num))
  have grow := (tendsto_rpow_atTop (by norm_num : 0 < (99/100:ℝ))).comp inf
  filter_upwards [hinf.eventually_ge_atTop 4, eventually_ge_atTop (1:ℕ),slow,
    grow.eventually_ge_atTop (max (Jmin:ℝ) 100)] with x hL hx hslow huge
  let L := Real.log (x:ℝ)
  let z := top d x
  let N := length d x
  have hL' : 4 ≤ L := hL
  have hl : 0 < L := by linarith
  have hxpos : (0:ℝ) < x := by exact_mod_cast hx
  change max (Jmin:ℝ) 100 ≤ (x:ℝ)^(99/100:ℝ) at huge
  change ‖L^(4:ℝ)‖ ≤ (1/2:ℝ)*‖(x:ℝ)^(1/100:ℝ)‖ at hslow
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl.le _), Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)] at hslow
  norm_num only [Real.rpow_ofNat] at hslow
  have hpow : 2*L^4 ≤ (x:ℝ)^(1/100:ℝ) := by linarith
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
  have hN : (x:ℝ)*(x:ℝ)^(99/100:ℝ) ≤ (N:ℝ) := length_lower hd hh hx hL hpow (by linarith)
  have hNup : (N:ℝ) ≤ z^2 / (Real.log z)^2 := Nat.floor_le (by positivity)
  intro a p q px hzpr hpq prime hzp
  change z ≤ (p:ℝ) at hzpr
  have hpr := hzpos.trans_le hzpr
  have ppos : 0 < p := by exact_mod_cast hpr
  let M := (N:ℝ)/p
  let J := N/p+1
  have hMJ : M ≤ (J:ℝ) := (div_le_iff₀ hpr).2 (by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul ppos).1 (Nat.lt_succ_self (N/p))).le)
  have hJM : (J:ℝ) ≤ M+1 := by
    dsimp [J,M]; push_cast
    exact add_le_add Nat.cast_div_le (le_refl (1:ℝ))
  have hMlow : (x:ℝ)^(99/100:ℝ) ≤ M := (le_div_iff₀ hpr).2 <| calc
    _ ≤ (x:ℝ)^(99/100:ℝ)*(x:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast px) (by positivity)
    _ = _ := mul_comm _ _
    _ ≤ _ := hN
  have hMup : M ≤ z/2 := (div_le_iff₀ hpr).2 <| calc
    (N:ℝ) ≤ z^2/(Real.log z)^2 := hNup
    _ ≤ z^2/(2:ℝ)^2 := by gcongr
    _ ≤ (z/2)*p := by nlinarith [mul_le_mul_of_nonneg_left hzpr hzpos.le, sq_nonneg z]
  have hJz : J ≤ ⌊z⌋₊ := (Nat.le_floor_iff hzpos.le).2 (by linarith)
  have hlogJ : (99/100)*L ≤ Real.log (J:ℝ) := by
    simpa only [Real.log_rpow hxpos] using Real.log_le_log (Real.rpow_pos_of_pos hxpos (99/100)) (hMlow.trans hMJ)
  have hmin : Jmin ≤ J := by exact_mod_cast ((le_max_left _ _).trans (huge.trans (hMlow.trans hMJ)))
  have h100 : (100:ℝ) ≤ M := (le_max_right _ _).trans (huge.trans hMlow)
  have hquot : (J:ℝ)/Real.log J ≤ (15/14)*(M/L) := calc
    _ ≤ ((101/100)*M)/((99/100)*L) := by gcongr; linarith
    _ ≤ _ := by
      have eq : ((101/100)*M)/((99/100)*L) = (101/99)*(M/L) := by ring
      rw [eq]
      exact mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg (by linarith) hl.le)
  obtain ⟨b,hb⟩ := charge_le_index_sieve (N := N) prime hzp a
  have incl : siftedIndices ⌊z⌋₊ (N/q+1) b ⊆ siftedIndices ⌊z⌋₊ J b := by
    intro i hi
    obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hI).trans_le (Nat.add_le_add_right (Nat.div_le_div_left hpq ppos) 1)),avoid⟩
  have embedded := hb.trans (Finset.card_le_card incl)
  rw [index_eq_cutoff] at embedded
  have found := hfilter J hmin ⌊z⌋₊ hJz b
  calc
    _ ≤ ((LargePrimeDeletion.cutoffSurvivors J ⌊z⌋₊ b).card:ℝ) := by exact_mod_cast embedded
    _ ≤ (21/10)*((J:ℝ)/Real.log J) := by convert found using 1 <;> norm_num
    _ ≤ (21/10)*((15/14)*(M/L)) := mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = (9/4)*(M/L) := by ring
    _ = _ := by unfold classUnit; dsimp [M,N,L]; ring

theorem uniform_progression {d : ℝ} (hd : 0 < d) (hh : d ≤ 1/2) :
    progressionBound (9/4) d := by
  filter_upwards [progression_at_reference hd hh] with x estimate
  intro a p hp
  obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hin
  have large : ⌊top d x⌋₊ < p := lt_of_not_ge fun h => hout (Nat.mem_primesLE.mpr ⟨h,prime⟩)
  have ref : top d x ≤ (p:ℝ) := (Nat.lt_floor_add_one _).le.trans
    (by exact_mod_cast (show ⌊top d x⌋₊+1 ≤ p by omega))
  exact estimate a p p le ref le_rfl prime large

end ProgressionFine687

#print axioms ProgressionFine687.uniform_progression
