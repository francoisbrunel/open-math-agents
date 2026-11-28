import Variance687
import DensiteCarree687
import Mertens687

/-! The frequency of square-window small-prime prefixes admitting even one
adversarial completion. Coordinates are taken on [0,H) before translation. -/
namespace ProfilsProlongeables687
open Distribution687 Transfert687 Filter
open scoped BigOperators

noncomputable def prefixes (z x H : ℕ) : Finset (Assignment z.primesLE) := by
  classical
  exact Finset.univ.filter (fun b => ∃ a : ℕ → ℕ,
    (∀ p : ↥z.primesLE, a p.val%p.val = (b p).val) ∧
    ∀ i < H, ∃ p ≤ x, p.Prime ∧ i%p=a p%p)

private theorem half_mean (P : Finset ℕ) (pr : ∀ p ∈ P, p.Prime) (H : ℕ)
    (F : Finset (Assignment P)) (V : ℝ) (v : V = ∏ p ∈ P, (1-(p:ℝ)⁻¹))
    (pos : 0 < (H:ℝ)*V)
    (thin : ∀ b ∈ F, ((misses P (Finset.range H) b).card:ℝ) ≤ (H:ℝ)*V/2) :
    (F.card:ℝ)*((H:ℝ)*V) ≤ 4*(Fintype.card (Assignment P):ℝ) := by
  classical
  let X := fun b : Assignment P => ((misses P (Finset.range H) b).card:ℝ)
  let μ := (H:ℝ)*V
  have mass : (Fintype.card (Assignment P):ℝ)*V = ∏ p ∈ P, ((p:ℝ)-1) := by
    rw [v]
    simp only [Assignment,Fintype.card_pi,Fintype.card_fin,Nat.cast_prod]
    rw [Finset.prod_coe_sort P (fun p : ℕ => (p:ℝ)),← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have nz : (p:ℝ) ≠ 0 := by exact_mod_cast (pr p hp).ne_zero
    field_simp
  have total := Variance687.variance_bound P pr H
  change (∑ b, (X b-(H:ℝ)*(∏ p ∈ P, (1-(p:ℝ)⁻¹)))^2) ≤ _ at total
  rw [← v,← mass] at total
  have hs : (F.card:ℝ)*(μ/2)^2 ≤ ∑ b, (X b-μ)^2 := calc
    _ = ∑ _b ∈ F, (μ/2)^2 := by simp
    _ ≤ ∑ b ∈ F, (X b-μ)^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have t : μ/2 ≤ μ-X b := by linarith [show X b ≤ μ/2 from thin b hb]
      have h := pow_le_pow_left₀ (show 0 ≤ μ/2 by dsimp only [μ]; linarith) t 2
      nlinarith only [h]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  apply (mul_le_mul_iff_left₀ pos).mp
  dsimp only [μ] at hs
  nlinarith only [hs,total]

private theorem shift {z x H : ℕ} (b : Assignment z.primesLE) (hb : b ∈ prefixes z x H) :
    ∃ a : ℕ → ℕ, (∀ n ∈ Finset.Icc 1 H, ∃ p ≤ x, p.Prime ∧ n%p=a p%p) ∧
      (misses z.primesLE (Finset.range H) b).card ≤ (survivors z H a).card := by
  classical
  obtain ⟨a,ha,cover⟩ := (Finset.mem_filter.mp hb).2
  refine ⟨fun p => a p+1,?_,?_⟩
  · intro n hn
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hn
    obtain ⟨p,px,pr,hit⟩ := cover (n-1) (by omega)
    refine ⟨p,px,pr,?_⟩
    change n ≡ a p+1 [MOD p]
    simpa only [Nat.sub_add_cancel lo] using (Nat.ModEq.add_right 1 hit)
  · apply Finset.card_le_card_of_injOn (fun i : ℕ => i+1)
    · intro i hi
      obtain ⟨iH,avoid⟩ := Finset.mem_filter.mp hi
      change i+1 ∈ survivors z H (fun p => a p+1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.succ_pos i,Finset.mem_range.mp iH⟩,?_⟩
      intro p hp hit
      apply avoid ⟨p,hp⟩
      have eqn : i%p = a p%p := Nat.ModEq.add_right_cancel' 1 hit
      exact eqn.trans (ha ⟨p,hp⟩)
    · intro i _ j _ h
      exact Nat.add_right_cancel h

/-- At most 12 log(z)/z² of all prefixes can be completed by the remaining
primes, whose residues may be chosen after the entire prefix is known. -/
theorem rare (m : ℕ) (hm : 144 ≤ m) :
    ∀ᶠ k : ℕ in atTop, let z := k^m
      ((prefixes z (k^(m+1)) (z^2)).card:ℝ)*(z:ℝ)^2 ≤
        12*(Fintype.card (Assignment z.primesLE):ℝ)*Real.log z := by
  filter_upwards [DensiteCarree687.thin_of_cover m (by omega),eventually_ge_atTop (3:ℕ)]
    with k thin hk
  let z := k^m
  let H := z^2
  let F := prefixes z (k^(m+1)) H
  let V := ∏ p ∈ z.primesLE, (1-(p:ℝ)⁻¹)
  have kp : 0 < k := by omega
  have mp : 1 ≤ m := by omega
  have hz : 3 ≤ z := hk.trans (by simpa only [z,pow_one] using Nat.pow_le_pow_right kp mp)
  have L : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1<z by omega))
  have primes : z.primesLE = (Finset.range (z+1)).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  have lb : 1/(3*Real.log z) ≤ V := by simpa only [V,primes,OMA_M3.Qm,one_div] using OMA_M3.main z hz
  have vp : 0<V := (one_div_pos.mpr (by positivity)).trans_le lb
  have zp : 0 < z := by omega
  have hp : 0<(H:ℝ) := by exact_mod_cast (show 0 < H from pow_pos zp 2)
  have sh (b : Assignment z.primesLE) (hb : b ∈ F) :
      ((misses z.primesLE (Finset.range H) b).card:ℝ) ≤ (H:ℝ)*V/2 := by
    obtain ⟨a,ac,inc⟩ := shift b hb
    have u := thin a ac
    have mpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
    have c : (24:ℝ)/m ≤ 1/6 := (div_le_iff₀ mpos).mpr (by linarith [show (144:ℝ) ≤ m by exact_mod_cast hm])
    calc
      _ ≤ ((survivors z H a).card:ℝ) := by exact_mod_cast inc
      _ ≤ _ := u
      _ ≤ (1/6)*(z:ℝ)^2/Real.log z := by gcongr
      _ = (H:ℝ)*(1/(3*Real.log z))/2 := by dsimp [H]; push_cast; field_simp; ring
      _ ≤ _ := by gcongr
  have bnd := half_mean z.primesLE (fun p hp => (Nat.mem_primesLE.mp hp).2) H F V rfl (mul_pos hp vp) sh
  have h := mul_le_mul_of_nonneg_left lb (mul_nonneg (Nat.cast_nonneg F.card) hp.le)
  have h' : (F.card:ℝ)*(H:ℝ)/(3*Real.log z) ≤ 4*(Fintype.card (Assignment z.primesLE):ℝ) := by
    calc
      _ = ((F.card:ℝ)*(H:ℝ))*(1/(3*Real.log z)) := by ring
      _ ≤ _ := h
      _ ≤ _ := by simpa only [mul_assoc] using bnd
  have endb := (div_le_iff₀ (by positivity)).mp h'
  dsimp only [H] at endb
  push_cast at endb
  change (F.card:ℝ)*(z:ℝ)^2 ≤ _
  linarith only [endb]

end ProfilsProlongeables687
#print axioms ProfilsProlongeables687.rare
