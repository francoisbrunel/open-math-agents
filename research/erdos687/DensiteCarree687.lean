import CribleFin687
import CribleTransfert687
import Harmonique687

/-! A positive lower density on square intervals at small-prime cutoffs
would give a saving in the exponent of x in Erdos 687(i). -/
namespace DensiteCarree687
open Filter Transfert687 Progressions687 CribleTransfert687
open OAI.Erdos970.NumberTheoryLean
open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2
open scoped Asymptotics BigOperators

private theorem row_bound {k m p Jmin : ℕ} (hk : 2 ≤ k) (hm : 2 ≤ m)
    (enough : Jmin ≤ k) (large : k^m < p) (last : p ≤ k^(m+1)) (prime : p.Prime)
    (sieve : ∀ J ≥ Jmin, ∀ z : ℕ, J ≤ z → ∀ b : ℕ → ℕ,
      ((LargePrimeDeletion.cutoffSurvivors J z b).card:ℝ) ≤ 3*((J:ℝ)/Real.log J))
    (a : ℕ → ℕ) :
    (charge (survivors (k^m) ((k^m)^2) a) a p:ℝ) ≤
      12*((k^m:ℕ):ℝ)^2/Real.log (k^m:ℕ)/p := by
  let z := k^m
  let J := z^2/p+1
  have kp : 0 < k := by omega
  have kz : k ≤ z := by simpa [z] using
    (Nat.pow_le_pow_right kp (show 1 ≤ m by omega))
  have zp : 0 < z := kp.trans_le kz
  have room : k^(m-1) ≤ z^2/p := (Nat.le_div_iff_mul_le prime.pos).2 <| calc
    k^(m-1)*p ≤ k^(m-1)*k^(m+1) := Nat.mul_le_mul_left _ last
    _ = z^2 := by rw [← pow_add]; dsimp [z]; rw [← pow_mul]; congr 1 <;> omega
  have kprev : k ≤ k^(m-1) := by
    simpa using Nat.pow_le_pow_right kp (show 1 ≤ m-1 by omega)
  have jlo : k ≤ J := by dsimp [J]; omega
  have jhi : J ≤ z := (Nat.div_lt_iff_lt_mul prime.pos).2 (by
    calc z^2 = z*z := pow_two _
         _ < z*p := Nat.mul_lt_mul_of_pos_left large zp)
  have square : z ≤ J^2 := calc
    z ≤ k^((m-1)*2) := Nat.pow_le_pow_right kp (by omega)
    _ = (k^(m-1))^2 := pow_mul _ _ _
    _ ≤ J^2 := Nat.pow_le_pow_left (by dsimp [J]; omega) _
  have zreal : (1:ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have jreal : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have logz := Real.log_pos zreal
  have logs : Real.log z ≤ 2*Real.log J := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (by positivity : 0 < (z:ℝ))
      (show (z:ℝ) ≤ (J:ℝ)^2 by exact_mod_cast square)
  have pp : (0:ℝ) < p := by exact_mod_cast prime.pos
  have pz : p ≤ z^2 := calc
    p ≤ k^(m+1) := last
    _ ≤ k^(m*2) := Nat.pow_le_pow_right kp (by omega)
    _ = z^2 := pow_mul _ _ _
  have one : 1 ≤ (z:ℝ)^2/p := (le_div_iff₀ pp).mpr (by simpa using (show (p:ℝ) ≤ (z:ℝ)^2 by exact_mod_cast pz))
  have ju : (J:ℝ) ≤ 2*((z:ℝ)^2/p) := by
    have h : (J:ℝ) ≤ (z:ℝ)^2/p+1 := by
      have cast : ((z^2:ℕ):ℝ) = (z:ℝ)^2 := by norm_cast
      change ((z^2/p+1:ℕ):ℝ) ≤ _
      rw [Nat.cast_add,Nat.cast_one,← cast]
      exact add_le_add (Nat.cast_div_le (α := ℝ) (m := z^2) (n := p)) (le_refl (1:ℝ))
    linarith
  obtain ⟨b,hit⟩ := charge_le_index_sieve (N := z^2) prime large a
  rw [index_eq_cutoff] at hit
  calc
    _ ≤ ((LargePrimeDeletion.cutoffSurvivors J z b).card:ℝ) := by exact_mod_cast hit
    _ ≤ 3*((J:ℝ)/Real.log J) := sieve J (enough.trans jlo) z jhi b
    _ ≤ 3*(2*((z:ℝ)^2/p)/(Real.log z/2)) := by gcongr <;> linarith
    _ = _ := by change _ = 12*(z:ℝ)^2/Real.log z/p; ring

/-- Every prime row in the entire power band is included in this estimate,
at every residue assignment. The factor tends to zero as m grows. -/
theorem power_band (m : ℕ) (hm : 2 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
    (∑ p ∈ (k^(m+1)).primesLE \ (k^m).primesLE,
      (charge (survivors (k^m) ((k^m)^2) a) a p:ℝ)) ≤
      (24/(m:ℝ))*((k^m:ℕ):ℝ)^2/Real.log (k^m:ℕ) := by
  obtain ⟨Jmin, h⟩ := eventually_atTop.mp (CribleFin687.asymptotic_interval 1 (by norm_num))
  have tans := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop (max Jmin 2), tans.eventually_ge_atTop 10] with k hk hklog
  intro a
  let z := k^m
  let x := k^(m+1)
  let P := x.primesLE \ z.primesLE
  have hk2 := (le_max_right _ _).trans hk
  have kp : 0 < k := by omega
  have kz : k ≤ z := by simpa [z] using Nat.pow_le_pow_right kp (show 1 ≤ m by omega)
  have z2 : 2 ≤ z := hk2.trans kz
  have zx : z ≤ x := Nat.pow_le_pow_right kp (by omega)
  have logz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have mp : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hband := Harmonique687.band_bound (show (2:ℝ) ≤ z by exact_mod_cast z2)
    (show (z:ℝ) ≤ x by exact_mod_cast zx)
  rw [Nat.floor_natCast] at hband
  have zl : Real.log z = (m:ℝ)*Real.log k := by simp [z,Real.log_pow]
  have xl : Real.log x = ((m:ℝ)+1)*Real.log k := by simp [x,Real.log_pow]
  change 10 ≤ Real.log k at hklog
  have hsum : (∑ p ∈ P, (1:ℝ)/p) ≤ 2/(m:ℝ) := by
    apply (le_div_iff₀ mp).mpr
    apply le_of_mul_le_mul_right (a := Real.log k) _ (by linarith)
    change Real.log z * (∑ p ∈ P, (1:ℝ)/p) ≤ Real.log x - Real.log z + 10 at hband
    rw [zl,xl] at hband
    nlinarith only [hband,hklog]
  change (∑ p ∈ P, _) ≤ (24/(m:ℝ))*(z:ℝ)^2/Real.log z
  calc
    _ ≤ ∑ p ∈ P, (12*(z:ℝ)^2/Real.log z)*(1/p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨last,prime⟩ := Nat.mem_primesLE.mp hin
      have large : z < p := lt_of_not_ge (fun e => hout (Nat.mem_primesLE.mpr ⟨e,prime⟩))
      simpa only [mul_one_div] using row_bound hk2 hm ((le_max_left _ _).trans hk) large last prime
        (fun J hJ z hz b => by convert h J hJ z hz b using 1 <;> norm_num) a
    _ = (12*(z:ℝ)^2/Real.log z)*(∑ p ∈ P, (1:ℝ)/p) := (Finset.mul_sum ..).symm
    _ ≤ (12*(z:ℝ)^2/Real.log z)*(2/(m:ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- In a full cover this bound holds on the very same residue profile
that the larger primes complete. -/
theorem thin_of_cover (m : ℕ) (hm : 2 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
      (∀ n ∈ Finset.Icc 1 ((k^m)^2), ∃ p ≤ k^(m+1), p.Prime ∧ n%p = a p%p) →
      ((survivors (k^m) ((k^m)^2) a).card:ℝ) ≤
        (24/(m:ℝ))*((k^m:ℕ):ℝ)^2/Real.log (k^m:ℕ) := by
  filter_upwards [power_band m hm] with k budget
  intro a covered
  apply le_trans _ (budget a)
  exact_mod_cast survivor_le_sum (z := k^m) a covered

private theorem mono : Monotone Erdos687.Y := by
  intro s t st
  apply csSup_le
  · exact ⟨0,fun _ => 0,by simp⟩
  · intro H h
    obtain ⟨a,all⟩ := h
    apply le_Y_of_covered
    refine ⟨a,fun n hn => ?_⟩
    obtain ⟨p,ps,pr,hit⟩ := all n hn
    exact ⟨p,ps.trans st,pr,hit⟩

private theorem interpolate (m : ℕ)
    (powers : ∀ᶠ k : ℕ in atTop, Erdos687.Y (k^(m+1)) ≤ (k^m)^2) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^((2*(m:ℝ))/(m+1))) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp powers
  let r := ((m:ℝ)+1)⁻¹
  have rp : 0 < r := by dsimp [r]; positivity
  have inf := (tendsto_rpow_atTop rp).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop)
  apply Asymptotics.IsBigO.of_bound ((2:ℝ)^(2*m))
  filter_upwards [inf.eventually_ge_atTop (max (K:ℝ) 1),eventually_ge_atTop (1:ℕ)] with x huge hx
  let w := (x:ℝ)^r
  let k := ⌈w⌉₊
  change max (K:ℝ) 1 ≤ w at huge
  have one : 1 ≤ w := (le_max_right _ _).trans huge
  have wn := (zero_le_one.trans one)
  have low : w ≤ (k:ℝ) := Nat.le_ceil _
  have kk : K ≤ k := by exact_mod_cast ((le_max_left _ _).trans (huge.trans low))
  have high : (k:ℝ) ≤ 2*w := by
    have ce : (k:ℝ) < w+1 := Nat.ceil_lt_add_one wn
    linarith
  have xn : 0 ≤ (x:ℝ) := Nat.cast_nonneg _
  have xid : w^(m+1) = (x:ℝ) := by
    dsimp [w]
    rw [← Real.rpow_mul_natCast xn]
    simp [r,show (m:ℝ)+1 ≠ 0 by positivity]
  have fits : x ≤ k^(m+1) := by
    exact_mod_cast (show (x:ℝ) ≤ (k:ℝ)^(m+1) by rw [← xid]; gcongr)
  have y := (mono fits).trans (hK k kk)
  have yreal : (Erdos687.Y x:ℝ) ≤ (k:ℝ)^(2*m) := by
    rw [Nat.mul_comm 2 m,pow_mul]
    exact_mod_cast y
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Real.rpow_nonneg xn _)]
  calc
    _ ≤ (2*w)^(2*m) := yreal.trans (pow_le_pow_left₀ (by positivity) high _)
    _ = _ := by
      rw [mul_pow]
      congr 1
      change ((x:ℝ)^r)^(2*m) = _
      rw [← Real.rpow_mul_natCast xn]
      congr 1
      push_cast
      dsimp [r]
      ring

/-- A thin small-prime profile that the larger prime rows actually complete. -/
def ThinCompletion (m k : ℕ) : Prop := ∃ a : ℕ → ℕ,
    ((survivors (k^m) ((k^m)^2) a).card:ℝ) ≤
      (24/(m:ℝ))*((k^m:ℕ):ℝ)^2/Real.log (k^m:ℕ) ∧
    ∀ n ∈ Finset.Icc 1 ((k^m)^2), ∃ p ≤ k^(m+1), p.Prime ∧ n%p = a p%p

theorem upper_of_no_thin_completions (m : ℕ) (hm : 2 ≤ m)
    (none : ∀ᶠ k : ℕ in atTop, ¬ ThinCompletion m k) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^((2*(m:ℝ))/(m+1))) := by
  apply interpolate
  filter_upwards [none,thin_of_cover m hm] with k no thin
  apply csSup_le
  · exact ⟨0,fun _ => 0,by simp⟩
  · intro H h
    obtain ⟨a,ha⟩ := h
    by_contra! big
    apply no
    have all : ∀ n ∈ Finset.Icc 1 ((k^m)^2), ∃ p ≤ k^(m+1), p.Prime ∧ n%p = a p%p := by
      intro n hn
      obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
      exact ha n (Finset.mem_Icc.mpr ⟨lo,hi.trans big.le⟩)
    exact ⟨a,thin a all,all⟩

theorem upper_power_of_square_density (m : ℕ) (hm : 2 ≤ m)
    (stock : ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
      (24/(m:ℝ))*((k^m:ℕ):ℝ)^2/Real.log (k^m:ℕ) <
        ((survivors (k^m) ((k^m)^2) a).card:ℝ)) :
    (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^((2*(m:ℝ))/(m+1))) := by
  apply upper_of_no_thin_completions m hm
  filter_upwards [stock] with k bound
  rintro ⟨a,thin,_⟩
  exact (not_le_of_gt (bound a)) thin

theorem power_saving_iff :
    (∃ α : ℝ, α < 2 ∧ (fun x : ℕ => (Erdos687.Y x:ℝ)) =O[atTop]
      (fun x : ℕ => (x:ℝ)^α)) ↔
    ∃ m : ℕ, 2 ≤ m ∧ ∀ᶠ k : ℕ in atTop, ¬ ThinCompletion m k := by
  constructor
  · rintro ⟨α,ha,upper⟩
    obtain ⟨m,hm⟩ := exists_nat_gt (max 2 (α/(2-α)))
    have big := (le_max_right _ _).trans_lt hm
    have m2 : (2:ℝ) < m := (le_max_left _ _).trans_lt hm
    have gap := (div_lt_iff₀ (show 0 < 2-α by linarith)).mp big
    let u := ((m:ℝ)+1)*α
    let v := 2*(m:ℝ)-u
    have vp : 0 < v := by dsimp [v,u]; linarith only [gap]
    obtain ⟨C,hC,est⟩ := upper.exists_pos
    obtain ⟨X,hX⟩ := eventually_atTop.mp est.bound
    have inf := (tendsto_rpow_atTop vp).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)
    refine ⟨m,by exact_mod_cast m2.le,?_⟩
    filter_upwards [eventually_ge_atTop (max X 1),inf.eventually_gt_atTop C] with k hk grows
    rintro ⟨a,_,all⟩
    have k1 := (le_max_right _ _).trans hk
    have kp : 0 < k := by omega
    have kr : 0 < (k:ℝ) := by exact_mod_cast kp
    have kx : k ≤ k^(m+1) := by simpa using Nat.pow_le_pow_right kp (show 1 ≤ m+1 by omega)
    have bound := hX (k^(m+1)) (((le_max_left _ _).trans hk).trans kx)
    have covered : (k^m)^2 ≤ Erdos687.Y (k^(m+1)) := le_Y_of_covered ⟨a,all⟩
    have scaled : ((k:ℝ)^(m+1))^α = (k:ℝ)^u := by
      rw [← Real.rpow_natCast (k:ℝ) (m+1),← Real.rpow_mul kr.le]
      simp [u]
    simp only [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      Nat.cast_pow,scaled] at bound
    change C < (k:ℝ)^v at grows
    have strict := mul_lt_mul_of_pos_left grows (Real.rpow_pos_of_pos kr u)
    have eq : (k:ℝ)^u*(k:ℝ)^v = ((k:ℝ)^m)^2 := by
      rw [← Real.rpow_add kr,show u+v=(m:ℝ)*2 by dsimp [v]; ring]
      simpa only [Nat.cast_ofNat, Real.rpow_natCast] using Real.rpow_mul_natCast kr.le (m:ℝ) 2
    rw [eq,mul_comm] at strict
    exact (not_lt_of_ge (show ((k:ℝ)^m)^2 ≤ C*(k:ℝ)^u from
      (show ((k:ℝ)^m)^2 ≤ Erdos687.Y (k^(m+1)) by exact_mod_cast covered).trans bound)) strict
  · rintro ⟨m,hm,none⟩
    refine ⟨2*(m:ℝ)/(m+1), (div_lt_iff₀ (by positivity)).mpr (by linarith),upper_of_no_thin_completions m hm none⟩

end DensiteCarree687
#print axioms DensiteCarree687.power_band
#print axioms DensiteCarree687.thin_of_cover
#print axioms DensiteCarree687.upper_power_of_square_density
#print axioms DensiteCarree687.power_saving_iff
