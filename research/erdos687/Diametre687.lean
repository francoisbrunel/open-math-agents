import Accroissements687

/-! Exact threshold and order of the strongest guarantee obtained
    by reserving one distinct new prime per uncovered position. -/
namespace Diametre687
open Extension687 Progressions687 Filter
open scoped Asymptotics

def Fits (k J : ℕ) : Prop := ∃ S ⊆ Finset.range J, S.card=k ∧ Admissible S
noncomputable def width (k : ℕ) : ℕ := sInf {J : ℕ | Fits k J}

theorem upper_witness {k : ℕ} (large : 256 ≤ k) : Fits k (128*⌈(k:ℝ)*Real.log k⌉₊+1) := by
  let t := ⌈(k:ℝ)*Real.log k⌉₊
  have kp : (0:ℝ)<k := by positivity
  have log1 : 1 ≤ Real.log (k:ℝ) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<4) (show (4:ℝ) ≤ k by exact_mod_cast (show 4 ≤ k by omega))
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at h
    norm_num at h; linarith [Real.log_two_gt_d9]
  have ceil : (k:ℝ)*Real.log k ≤ t := Nat.le_ceil _
  have kt : k ≤ t := by
    exact_mod_cast (show (k:ℝ) ≤ t by nlinarith [mul_le_mul_of_nonneg_left log1 kp.le])
  have tcap : t ≤ k^2 := by
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos kp) kp.le]
  have tp : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have logt := Real.log_pos (show (1:ℝ)<t by exact_mod_cast (show 1<t by omega))
  have compare := Real.log_le_log tp (show (t:ℝ) ≤ (k:ℝ)^2 by exact_mod_cast tcap)
  rw [Real.log_pow] at compare
  norm_num at compare
  have supply := Croissance687.prime_supply (by omega : 128 ≤ t)
  have enough : k ≤ ((128*t).primesLE \ t.primesLE).card := by
    have est : (k:ℝ) ≤ 8*t/Real.log t := (le_div_iff₀ logt).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left compare kp.le])
    exact_mod_cast est.trans supply
  have wider : (128*t).primesLE \ t.primesLE ⊆ (128*t).primesLE \ k.primesLE := by
    intro q hq
    obtain ⟨inside,outside⟩ := Finset.mem_sdiff.mp hq
    exact Finset.mem_sdiff.mpr ⟨inside,fun h => outside (Nat.primesLE_mono kt h)⟩
  exact (capacity_iff_tuple (z := k) (k := k) le_rfl).mp
    (Roue687.prime_tuple_barrier le_rfl (enough.trans (Finset.card_le_card wider)))

theorem fits_width (k : ℕ) : Fits k (width k) := by
  change sInf {J : ℕ | Fits k J} ∈ {J : ℕ | Fits k J}
  apply Nat.sInf_mem
  let K := max 256 k
  obtain ⟨S,sub,n,adm⟩ := upper_witness (k := K) (le_max_left ..)
  have enough : k ≤ S.card := by rw [n]; exact le_max_right ..
  obtain ⟨T,part,card⟩ := Finset.exists_subset_card_eq enough
  refine ⟨_,T,part.trans sub,card,?_⟩
  intro p hp
  obtain ⟨r,lt,avoid⟩ := adm p hp
  exact ⟨r,lt,fun i hi => avoid i (part hi)⟩

theorem threshold {z J k : ℕ} (kz : k ≤ z) :
    (∃ b, k ≤ (siftedIndices z J b).card) ↔ width k ≤ J := by
  rw [capacity_iff_tuple kz]
  constructor
  · exact fun h => Nat.sInf_le (s := {J : ℕ | Fits k J}) h
  · intro h
    obtain ⟨S,sub,card,adm⟩ := fits_width k
    exact ⟨S,sub.trans (Finset.range_mono h),card,adm⟩

theorem length_bounds {k : ℕ} (large : 256 ≤ k) :
    (k:ℝ)*Real.log k ≤ 17*width k ∧ (width k:ℝ) ≤ 257*((k:ℝ)*Real.log k) := by
  let D := width k
  obtain ⟨S,sub,card,adm⟩ := fits_width k
  have kd : k ≤ D := by simpa only [card,Finset.card_range] using Finset.card_le_card sub
  have kp : (0:ℝ)<k := by positivity
  have logd := Real.log_pos (show (1:ℝ)<D by exact_mod_cast (show 1<D by omega))
  have logk := Real.log_le_log kp (show (k:ℝ) ≤ D by exact_mod_cast kd)
  obtain ⟨b,cap⟩ := (threshold (z := D) (J := D) kd).mpr le_rfl
  have upper := Accroissements687.extreme (by omega : 256 ≤ D)
    (show D ≤ D^8 by simpa using Nat.pow_le_pow_right (by omega : 0<D) (by norm_num : 1 ≤ 8)) b
  have lk := (le_div_iff₀ logd).mp ((show (k:ℝ) ≤ (siftedIndices D D b).card by exact_mod_cast cap).trans upper)
  have min : D ≤ 128*⌈(k:ℝ)*Real.log k⌉₊+1 := Nat.sInf_le (s := {J : ℕ | Fits k J}) (upper_witness large)
  have pos := Real.log_nonneg (show (1:ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega))
  have c := Nat.ceil_lt_add_one (mul_nonneg kp.le pos)
  have ll := Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ) ≤ k by exact_mod_cast (show 2 ≤ k by omega))
  have kr : 256 ≤ (k:ℝ) := by exact_mod_cast large
  have one : 1 ≤ (k:ℝ)*Real.log k := by
    nlinarith [mul_le_mul_of_nonneg_left ll kp.le,
      mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_gt_d9) kp.le]
  have minR : (D:ℝ) ≤ 128*(⌈(k:ℝ)*Real.log k⌉₊:ℝ)+1 := by exact_mod_cast min
  exact ⟨(mul_le_mul_of_nonneg_left logk kp.le).trans lk,by change (D:ℝ) ≤ _; linarith⟩

theorem order : (fun k : ℕ => (width k:ℝ)) =Θ[atTop] (fun k => (k:ℝ)*Real.log k) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 257
    filter_upwards [eventually_ge_atTop (256:ℕ)] with k hk
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))] using (length_bounds hk).2
  · apply Asymptotics.IsBigO.of_bound 17
    filter_upwards [eventually_ge_atTop (256:ℕ)] with k hk
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))] using (length_bounds hk).1

theorem guaranteed_gain {x z r : ℕ} (zx : z ≤ x) (rz : r+1 ≤ z)
    (fresh : r ≤ (x.primesLE \ z.primesLE).card) :
    Erdos687.Y z+(width (r+1)-1) ≤ Erdos687.Y x := by
  apply growth_from_capacity zx
  intro b
  obtain ⟨S,sub,card,_⟩ := fits_width (r+1)
  have kd : r+1 ≤ width (r+1) := by simpa only [card,Finset.card_range] using Finset.card_le_card sub
  have no : ¬r+1 ≤ (siftedIndices z (width (r+1)-1) b).card := by
    intro h
    have imp := (threshold rz).mp ⟨b,h⟩
    omega
  omega

end Diametre687
