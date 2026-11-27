import Extension687

/-! Exact criterion for the residual search when each class hits at most two
    uncovered points. Colours are the primes available for the final stage. -/
namespace Paires687

def Covered (S P : Finset ℕ) := ∃ a : ℕ → ℕ, ∀ i ∈ S, ∃ p ∈ P, i%p = a p%p

/-- A family of disjoint two-point sets, each lying in one class of its
    own modulus. The last inequality reserves a fresh modulus per singleton. -/
def PairBudget (S P : Finset ℕ) : Prop :=
  ∃ Q ⊆ P, ∃ B : ℕ → Finset ℕ, ∃ a : ℕ → ℕ,
    (∀ p ∈ Q, (B p).card = 2 ∧ ∀ i ∈ B p, i ∈ S ∧ i%p = a p%p) ∧
    (Q : Set ℕ).PairwiseDisjoint B ∧ S.card ≤ P.card+Q.card

/-- This direction works even when some residue classes have higher capacity. -/
theorem covered_of_pairs {S P : Finset ℕ} (h : PairBudget S P) : Covered S P := by
  classical
  obtain ⟨Q,hQ,B,a,hB,dis,budget⟩ := h
  let T := Q.biUnion B
  have sub : T ⊆ S := by
    intro i hi
    obtain ⟨p,hp,h⟩ := Finset.mem_biUnion.mp hi
    exact ((hB p hp).2 i h).1
  have cardT : T.card = Q.card*2 := calc
    _ = ∑ p ∈ Q, (B p).card := Finset.card_biUnion dis
    _ = ∑ _p ∈ Q, 2 := Finset.sum_congr rfl fun p hp => (hB p hp).1
    _ = _ := by simp
  have rest : (S \ T).card ≤ (P \ Q).card := by
    rw [Finset.card_sdiff_of_subset sub,Finset.card_sdiff_of_subset hQ,cardT]
    omega
  obtain ⟨r,hr⟩ := Extension687.assign_images _ _ id rest
  refine ⟨fun p => if p ∈ Q then a p else r p,?_⟩
  intro i hi
  by_cases ht : i ∈ T
  · obtain ⟨p,hp,h⟩ := Finset.mem_biUnion.mp ht
    exact ⟨p,hQ hp,by simpa only [if_pos hp] using ((hB p hp).2 i h).2⟩
  · obtain ⟨p,hp,eqn⟩ := hr i (Finset.mem_sdiff.mpr ⟨hi,ht⟩)
    obtain ⟨pin,pout⟩ := Finset.mem_sdiff.mp hp
    exact ⟨p,pin,by simp only [if_neg pout,eqn,id_eq]⟩

theorem covered_iff_pairs {S P : Finset ℕ}
    (cap : ∀ p ∈ P, ∀ r : ℕ, (S.filter fun i => i%p = r%p).card ≤ 2) :
    Covered S P ↔ PairBudget S P := by
  classical
  refine ⟨?_,covered_of_pairs⟩
  rintro ⟨a,ha⟩
  let f (i : ℕ) := if hi : i ∈ S then Classical.choose (ha i hi) else 0
  have hf (i : ℕ) (hi : i ∈ S) : f i ∈ P ∧ i%(f i) = a (f i)%(f i) := by
    simpa only [f,dif_pos hi] using Classical.choose_spec (ha i hi)
  let B (p : ℕ) := S.filter fun i => f i = p
  let Q := P.filter fun p => (B p).card = 2
  have sub : Q ⊆ P := Finset.filter_subset _ _
  have eqn (p : ℕ) (i : ℕ) (hi : i ∈ B p) : i ∈ S ∧ i%p = a p%p := by
    obtain ⟨his,he⟩ := Finset.mem_filter.mp hi
    exact ⟨his,he ▸ (hf i his).2⟩
  refine ⟨Q,sub,B,a,fun p hp => ⟨(Finset.mem_filter.mp hp).2,eqn p⟩,?_,?_⟩
  · intro p hp q hq hne
    exact Finset.disjoint_left.mpr fun i hi hj => hne
      ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
  · calc S.card = ∑ p ∈ P, (B p).card :=
           Finset.card_eq_sum_card_fiberwise fun i hi => (hf i hi).1
         _ ≤ ∑ p ∈ P, (1 + if (B p).card = 2 then 1 else 0) := by
           apply Finset.sum_le_sum
           intro p hp
           have le : (B p).card ≤ 2 := (Finset.card_le_card
             (show B p ⊆ S.filter (fun i => i%p = a p%p) from fun i hi =>
               Finset.mem_filter.mpr (eqn p i hi))).trans (cap p hp (a p))
           split <;> omega
         _ = _ := by simp [Finset.sum_add_distrib,Q]

end Paires687
