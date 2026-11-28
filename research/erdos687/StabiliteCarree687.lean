import CentreCarre687

/-! Stability of the number of survivors when a set of prime rows is
changed. The bound uses the total reciprocal mass of the changed primes. -/
namespace StabiliteCarree687
open Filter Transfert687 Progressions687 CribleTransfert687
open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

private theorem other_row {z N p : ℕ} (hp : p.Prime) (a : ℕ → ℕ) (r : ℕ) :
    ∃ b₀ b₁ : ℕ → ℕ,
      ((survivors z N a).filter fun n => n%p=r%p).card ≤
      (siftedIndices z (N/p+1) b₀).card + (siftedIndices z (N/p+1) b₁).card := by
  classical
  let t (q : ℕ) := if h : p.Coprime q then (Nat.chineseRemainder h r (a q)).val else 0
  let b (e q : ℕ) := if q=p then e else t q / p
  refine ⟨b 0,b 1,?_⟩
  refine le_trans ?_ (Finset.card_union_le (siftedIndices z (N/p+1) (b 0)) (siftedIndices z (N/p+1) (b 1)))
  apply Finset.card_le_card_of_injOn (fun n : ℕ => n/p)
  · intro n hn
    obtain ⟨hs,hr⟩ := Finset.mem_filter.mp hn
    obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hs
    have fits : n/p ∈ Finset.range (N/p+1) := Finset.mem_range.mpr <|
      Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp hi).2)
    have embed (e : ℕ) (ep : (n/p)%p ≠ e%p) : n/p ∈ siftedIndices z (N/p+1) (b e) := by
      refine Finset.mem_filter.mpr ⟨fits,?_⟩
      intro q hq
      by_cases eq : q=p
      · subst q
        simpa [b] using ep
      · intro hit
        have co := (Nat.coprime_primes hp (Nat.mem_primesLE.mp hq).2).mpr (Ne.symm eq)
        have crt : t q ≡ r [MOD p] ∧ t q ≡ a q [MOD q] := by
          dsimp only [t]
          rw [dif_pos co]
          exact (Nat.chineseRemainder co r (a q)).property
        have idx : n/p ≡ t q/p [MOD q] := by simpa [Nat.ModEq,b,eq] using hit
        have same : n ≡ t q [MOD q] := calc
          n = n%p+p*(n/p) := (Nat.mod_add_div _ _).symm
          _ ≡ n%p+p*(t q/p) [MOD q] := (idx.mul_left p).add_left (n%p)
          _ = t q := by rw [hr.trans crt.1.symm,Nat.mod_add_div]
        exact avoid q hq (same.trans crt.2)
    by_cases zero : (n/p)%p=0
    · exact Finset.mem_union_right _ (embed 1 (by simp [zero,Nat.mod_eq_of_lt hp.one_lt]))
    · exact Finset.mem_union_left _ (embed 0 (by simpa using zero))
  · intro n hn m hm eq
    have rem := (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
    calc n = n%p+p*(n/p) := (Nat.mod_add_div _ _).symm
         _ = m%p+p*(m/p) := by rw [rem,show n/p=m/p from eq]
         _ = _ := Nat.mod_add_div _ _

private theorem row_cost {z p : ℕ} (hz : 1024 ≤ z) (hp : p.Prime) (pz : p ≤ z)
    (a : ℕ → ℕ) (r : ℕ) :
    (((survivors z (z^2) a).filter fun n => n%p=r%p).card:ℝ) ≤
      68*(z:ℝ)^2/Real.log z/p := by
  let J := z^2/p+1
  have lo : z ≤ J := by
    have h : z ≤ z^2/p := (Nat.le_div_iff_mul_le hp.pos).2 (by simpa [pow_two] using Nat.mul_le_mul_left z pz)
    dsimp [J]; omega
  have up : J ≤ z^2+1 := Nat.add_le_add_right (Nat.div_le_self _ _) 1
  have root : Nat.nthRoot 8 J ≤ z := by
    apply Nat.le_of_lt_succ
    apply (Nat.nthRoot_lt_iff (by decide : 8 ≠ 0)).2
    calc J ≤ z^2+1 := up
         _ < (z+1)^2 := by nlinarith
         _ ≤ (z+1)^8 := pow_le_pow_right₀ (by omega) (by decide)
  have lp : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have jl := Real.log_le_log (by positivity : 0 < (z:ℝ)) (show (z:ℝ) ≤ J by exact_mod_cast lo)
  have sieve (b : ℕ → ℕ) : ((siftedIndices z J b).card : ℝ) ≤ 17*((J:ℝ)/Real.log J) := by
    rw [index_eq_cutoff]
    simpa only [mul_div_assoc] using SquarefreeHarmonic.cutoffSurvivors_le_seventeen J z b (by omega) root
  have pp : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have pN : p ≤ z^2 := pz.trans (by nlinarith)
  have one : 1 ≤ (z:ℝ)^2/p := (le_div_iff₀ pp).mpr (by simpa using (show (p:ℝ) ≤ (z:ℝ)^2 by exact_mod_cast pN))
  have ju : (J:ℝ) ≤ 2*((z:ℝ)^2/p) := by
    have h : (J:ℝ) ≤ (z:ℝ)^2/p+1 := by
      have cast : ((z^2:ℕ):ℝ) = (z:ℝ)^2 := by norm_cast
      change ((z^2/p+1:ℕ):ℝ) ≤ _
      rw [Nat.cast_add,Nat.cast_one,← cast]
      exact add_le_add (Nat.cast_div_le (α := ℝ) (m := z^2) (n := p)) (le_refl (1:ℝ))
    linarith
  obtain ⟨b₀,b₁,h⟩ := other_row (z := z) (N := z^2) hp a r
  calc
    _ ≤ ((siftedIndices z J b₀).card:ℝ)+(siftedIndices z J b₁).card := by exact_mod_cast h
    _ ≤ 34*((J:ℝ)/Real.log J) := by linarith only [sieve b₀,sieve b₁]
    _ ≤ 34*(2*((z:ℝ)^2/p)/Real.log z) := by gcongr
    _ = _ := by ring

def changes (z : ℕ) (a b : ℕ → ℕ) := z.primesLE.filter fun p => a p%p ≠ b p%p

/-- An estimate in either direction, for every pair of residue assignments. -/
theorem stability {z : ℕ} (hz : 1024 ≤ z) (a b : ℕ → ℕ) :
    ((survivors z (z^2) a).card:ℝ) ≤ (survivors z (z^2) b).card +
      (68*(z:ℝ)^2/Real.log z)*(∑ p ∈ changes z a b, (1:ℝ)/p) := by
  classical
  let S := survivors z (z^2) a
  let T := survivors z (z^2) b
  let E := changes z a b
  let C (p : ℕ) := S.filter fun n => n%p=b p%p
  have sub : S ⊆ T ∪ E.biUnion C := by
    intro n hn
    by_cases ht : n ∈ T
    · exact Finset.mem_union_left _ ht
    · obtain ⟨hi,avoid⟩ := Finset.mem_filter.mp hn
      have notAll : ¬ ∀ p ∈ z.primesLE, n%p ≠ b p%p := fun v => ht (Finset.mem_filter.mpr ⟨hi,v⟩)
      push Not at notAll
      obtain ⟨p,hp,hit⟩ := notAll
      have changed : p ∈ E := Finset.mem_filter.mpr ⟨hp,fun same => avoid p hp (hit.trans same.symm)⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,changed,Finset.mem_filter.mpr ⟨hn,hit⟩⟩)
  have card := (Finset.card_le_card sub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left Finset.card_biUnion_le _))
  change (S.card:ℝ) ≤ T.card + _
  calc
    _ ≤ (T.card:ℝ)+∑ p ∈ E, ((C p).card:ℝ) := by exact_mod_cast card
    _ ≤ (T.card:ℝ)+∑ p ∈ E, (68*(z:ℝ)^2/Real.log z)*(1/p) := by
      refine add_le_add le_rfl ?_
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨pz,pr⟩ := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      simpa only [mul_one_div] using row_cost hz pr pz a (b p)
    _ = _ := by rw [Finset.mul_sum]

/-- Every complete profile has a positive harmonic distance from every
locally aligned profile. The lower bound is independent of the cutoff. -/
theorem separation (m : ℕ) (hm : 2 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℕ → ℕ,
    (∀ n ∈ Finset.Icc 1 ((k^m)^2), ∃ p ≤ k^(m+1), p.Prime ∧ n%p=a p%p) →
    ∀ b ∈ Finset.Icc 1 ((k^m)^2),
      1/64-(24:ℝ)/m ≤ 68*(∑ p ∈ changes (k^m) (fun _ => b) a, (1:ℝ)/p) := by
  filter_upwards [DensiteCarree687.thin_of_cover m hm,eventually_ge_atTop (1024:ℕ)] with k thin hk
  intro a full b hb
  let z := k^m
  have kz : k ≤ z := by simpa [z] using Nat.pow_le_pow_right (by omega : 0 < k) (show 1 ≤ m by omega)
  have zlarge := hk.trans kz
  let W := (z:ℝ)^2/Real.log z
  have lp : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have wp : 0 < W := by dsimp [W]; positivity
  have stock := CentreCarre687.aligned_stock (by omega : 512 ≤ z) hb (fun _ => b) (fun _ _ => rfl)
  have diff := stability zlarge (fun _ => b) a
  have small := thin a full
  apply le_of_mul_le_mul_right (a := W) _ wp
  have s1 : (z:ℝ)^2/(64*Real.log z)=(1/64:ℝ)*W := by dsimp [W]; ring
  have s2 : 68*(z:ℝ)^2/Real.log z=68*W := by dsimp [W]; ring
  have s3 : (24/(m:ℝ))*(z:ℝ)^2/Real.log z=(24/m)*W := by dsimp [W]; ring
  change _ ≤ (24/(m:ℝ))*(z:ℝ)^2/Real.log z at small
  rw [s1] at stock
  rw [s2] at diff
  rw [s3] at small
  change (1/64-24/(m:ℝ))*W ≤ (68*(∑ p ∈ changes z (fun _ => b) a, (1:ℝ)/p))*W
  nlinarith only [stock,diff,small]

end StabiliteCarree687
#print axioms StabiliteCarree687.stability
#print axioms StabiliteCarree687.separation
