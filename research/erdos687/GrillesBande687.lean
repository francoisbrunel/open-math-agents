import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.ModEq

/-! A bipartite rectangle among residue pairs in a short interval.
The counting step is the elementary Kővári–Sós–Turán bound for K₂,₂. -/
namespace GrillesBande687
open scoped BigOperators

private theorem incidence (U V : Finset ℕ) (N : ℕ → Finset ℕ)
    (inside : ∀ v ∈ V, N v ⊆ U)
    (many : V.card*(U.card^2+(∑ v ∈ V, (N v).card)) < (∑ v ∈ V, (N v).card)^2) :
    ∃ v ∈ V, ∃ w ∈ V, v ≠ w ∧ ∃ a ∈ N v, ∃ b ∈ N v, a≠b ∧ a∈N w ∧ b∈N w := by
  classical
  by_contra no
  have dis : (V : Set ℕ).PairwiseDisjoint (fun v => (N v).offDiag) := by
    intro v hv w hw ne
    apply Finset.disjoint_left.mpr
    intro t ht hu
    obtain ⟨a,b,d⟩ := Finset.mem_offDiag.mp ht
    obtain ⟨c,e,_⟩ := Finset.mem_offDiag.mp hu
    exact no ⟨v,hv,w,hw,ne,t.1,a,t.2,b,d,c,e⟩
  have sub : V.biUnion (fun v => (N v).offDiag) ⊆ U.offDiag := by
    intro t ht
    obtain ⟨v,hv,found⟩ := Finset.mem_biUnion.mp ht
    exact Finset.offDiag_mono (inside v hv) found
  have total := Finset.card_le_card sub
  rw [Finset.card_biUnion dis] at total
  have per (v : ℕ) : (N v).card^2=(N v).offDiag.card+(N v).card := by
    rw [Finset.offDiag_card]
    have t : (N v).card ≤ (N v).card*(N v).card := by
      by_cases zero : (N v).card=0
      · simp [zero]
      · simpa using Nat.mul_le_mul_left (N v).card (show 1 ≤ (N v).card by omega)
    rw [Nat.sub_add_cancel t,pow_two]
  have squares : (∑ v ∈ V, (N v).card^2) ≤ U.card^2+∑ v ∈ V, (N v).card := by
    simp_rw [per,Finset.sum_add_distrib]
    exact Nat.add_le_add_right (total.trans (by rw [Finset.offDiag_card,pow_two]; omega)) _
  have cs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul V
    (r := fun v => (N v).card) (f := fun _ => (1:ℕ)) (g := fun v => (N v).card^2)
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) (fun _ _ => by simp)
  have cs' : (∑ v ∈ V, (N v).card)^2 ≤ V.card*∑ v ∈ V, (N v).card^2 := by simpa using cs
  exact (not_lt_of_ge (cs'.trans (Nat.mul_le_mul_left V.card squares))) many

/-- The window may be translated; only injectivity of the joint residue
map on the test set is used. In [1,H] with coprime p,q and H<pq this
injectivity is automatic. -/
theorem rectangle (S : Finset ℕ) {p q : ℕ} (hp : 0<p) (hq : 0<q)
    (inj : ∀ i ∈ S, ∀ j ∈ S, i%p=j%p → i%q=j%q → i=j)
    (many : q*(p^2+S.card)<S.card^2) :
    ∃ a b c d : ℕ, a≠b ∧ c≠d ∧
      ∀ r ∈ ({a,b}:Finset ℕ), ∀ s ∈ ({c,d}:Finset ℕ), ∃ n ∈ S, n%p=r ∧ n%q=s := by
  classical
  let C (v : ℕ) := S.filter (fun n => n%q=v)
  let N (v : ℕ) := (C v).image (fun n => n%p)
  have size (v : ℕ) : (N v).card=(C v).card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj eq
    obtain ⟨is,ie⟩ := Finset.mem_filter.mp hi
    obtain ⟨js,je⟩ := Finset.mem_filter.mp hj
    exact inj i is j js eq (ie.trans je.symm)
  have total : (∑ v ∈ Finset.range q, (N v).card)=S.card := by
    simp_rw [size]
    exact (Finset.card_eq_sum_card_fiberwise (f := fun n => n%q)
      (fun n (_ : n∈S) => Finset.mem_range.mpr (Nat.mod_lt n hq))).symm
  have sub (v : ℕ) (_ : v∈Finset.range q) : N v ⊆ Finset.range p := by
    intro t ht
    obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  obtain ⟨c,_,d,_,cd,a,ac,b,bc,ab,ad,bd⟩ := incidence (Finset.range p) (Finset.range q) N sub
    (by simpa only [Finset.card_range,total] using many)
  refine ⟨a,b,c,d,ab,cd,?_⟩
  intro r hr s hs
  have cell : r ∈ N s := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr hs
    rcases hr with rfl|rfl <;> rcases hs with rfl|rfl <;> assumption
  obtain ⟨n,hn,eq⟩ := Finset.mem_image.mp cell
  exact ⟨n,(Finset.mem_filter.mp hn).1,eq,(Finset.mem_filter.mp hn).2⟩

theorem short_injective {H p q : ℕ} (co : p.Coprime q) (short : H < p*q)
    (S : Finset ℕ) (bound : ∀ i∈S, i≤H) :
    ∀ i ∈ S, ∀ j ∈ S, i%p=j%p → i%q=j%q → i=j := by
  intro i hi j hj ep eq
  have both : i ≡ j [MOD p*q] := (Nat.modEq_and_modEq_iff_modEq_mul co).mp ⟨ep,eq⟩
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt ((bound i hi).trans_lt short),
    Nat.mod_eq_of_lt ((bound j hj).trans_lt short)] using both

end GrillesBande687
#print axioms GrillesBande687.rectangle
#print axioms GrillesBande687.short_injective
