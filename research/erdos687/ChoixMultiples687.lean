import Extension687
import SurvieTotale687

/-! Exact finite reduction of the residual covering problem. Look only at
    classes hitting at least two points; unused moduli then cover singletons. -/
namespace ChoixMultiples687
open SurvieTotale687

theorem threshold (S P : Finset ℕ) (k : ℕ) :
    (∃ a, (remaining S P a).card ≤ k) ↔
    ∃ Q ⊆ P, ∃ a, (∀ p ∈ Q, 2 ≤ Transfert687.charge S a p) ∧
      (remaining S Q a).card ≤ (P \ Q).card + k := by
  classical
  constructor
  · rintro ⟨a,ok⟩
    let B (p : ℕ) := S.filter fun n => n%p = a p%p
    let Q := P.filter fun p => 2 ≤ (B p).card
    refine ⟨Q,Finset.filter_subset _ _,a,fun p hp => (Finset.mem_filter.mp hp).2,?_⟩
    have incl : remaining S Q a ⊆ remaining S P a ∪ (P \ Q).biUnion B := by
      intro n hn
      obtain ⟨ns,hq⟩ := Finset.mem_filter.mp hn
      by_cases stays : ∀ p ∈ P, n%p ≠ a p%p
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ns,stays⟩)
      · push Not at stays
        obtain ⟨p,hp,hit⟩ := stays
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨p,Finset.mem_sdiff.mpr ⟨hp,fun u => hq p u hit⟩,Finset.mem_filter.mpr ⟨ns,hit⟩⟩)
    have cap : ((P \ Q).biUnion B).card ≤ (P \ Q).card := calc
      _ ≤ ∑ p ∈ P \ Q, (B p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ P \ Q, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨pin,pout⟩ := Finset.mem_sdiff.mp hp
        have no : ¬ 2 ≤ (B p).card := fun h => pout (Finset.mem_filter.mpr ⟨pin,h⟩)
        omega
      _ = _ := by simp
    have count := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
    omega
  · rintro ⟨Q,sub,a,_,cost⟩
    let R := P \ Q
    let T := remaining S Q a
    obtain ⟨U,uu,uc⟩ := Finset.exists_subset_card_eq (min_le_left T.card R.card)
    obtain ⟨b,assigned⟩ := Extension687.assign_images U R id (uc.trans_le (min_le_right ..))
    let f (p : ℕ) := if p ∈ Q then a p else b p
    refine ⟨f,?_⟩
    have incl : remaining S P f ⊆ T \ U := by
      intro n hn
      obtain ⟨ns,avoid⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨ns,?_⟩,?_⟩
      · intro p hp
        simpa only [f,if_pos hp] using avoid p (sub hp)
      · intro hu
        obtain ⟨p,hp,h⟩ := assigned n hu
        obtain ⟨pin,pout⟩ := Finset.mem_sdiff.mp hp
        exact avoid p pin (by simp only [f,if_neg pout,h,id_eq])
    have left := Finset.card_le_card incl
    rw [Finset.card_sdiff_of_subset uu,uc] at left
    change T.card ≤ R.card+k at cost
    omega

theorem completes (S P : Finset ℕ) :
    Extension687.Completes S P ↔ ∃ Q ⊆ P, ∃ a,
      (∀ p ∈ Q, 2 ≤ Transfert687.charge S a p) ∧ (remaining S Q a).card ≤ (P \ Q).card := by
  have eq : Extension687.Completes S P ↔ ∃ a, (remaining S P a).card ≤ 0 := by
    constructor
    · rintro ⟨a,ha⟩
      refine ⟨a,?_⟩
      have empty : remaining S P a = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨ns,avoid⟩ := Finset.mem_filter.mp hn
        obtain ⟨p,hp,hit⟩ := ha n ns
        exact avoid p hp hit
      simp [empty]
    · rintro ⟨a,ha⟩
      refine ⟨a,fun n hn => ?_⟩
      by_contra! fail
      have inside : n ∈ remaining S P a := Finset.mem_filter.mpr ⟨hn,fail⟩
      exact (Nat.not_lt_of_ge ha) (Finset.card_pos.mpr ⟨n,inside⟩)
  simpa only [Nat.add_zero] using eq.trans (threshold S P 0)

end ChoixMultiples687
