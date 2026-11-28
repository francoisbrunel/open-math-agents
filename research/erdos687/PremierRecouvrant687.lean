import DispersionBande687

/-! Disjoint counting by the least covering prime. Pairing that one
prime with every later hit counts duplicates with their exact weight. -/
namespace PremierRecouvrant687
open Finset DispersionBande687

def hitSet (P : Finset ℕ) (a : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  P.filter (fun p => n%p=a p%p)

def firstRow (S P : Finset ℕ) (a : ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  S.filter (fun n => n%p=a p%p ∧ ∀ r ∈ P, r<p → n%r ≠ a r%r)

private theorem first_iff (S P : Finset ℕ) (a : ℕ → ℕ) {n p : ℕ}
    (hn : n ∈ S) (hp : p ∈ P) (ne : (hitSet P a n).Nonempty) :
    n ∈ firstRow S P a p ↔ p=(hitSet P a n).min' ne := by
  let K := hitSet P a n
  have least : K.min' ne ∈ K := K.min'_mem ne
  constructor
  · intro yes
    obtain ⟨_,hit,before⟩ := mem_filter.mp yes
    have member : p ∈ K := mem_filter.mpr ⟨hp,hit⟩
    apply le_antisymm _ (K.min'_le _ member)
    by_contra! less
    exact before _ (mem_filter.mp least).1 less (mem_filter.mp least).2
  · rintro rfl
    refine mem_filter.mpr ⟨hn,(mem_filter.mp least).2,?_⟩
    intro r hr earlier eq
    exact earlier.not_ge (K.min'_le _ (mem_filter.mpr ⟨hr,eq⟩))

theorem first_count (S P : Finset ℕ) (a : ℕ → ℕ) :
    (∑ p ∈ P, (firstRow S P a p).card) =
      (S.filter (fun n => (hitSet P a n).Nonempty)).card := by
  classical
  simp only [firstRow,card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  by_cases ne : (hitSet P a n).Nonempty
  · rw [if_pos ne]
    let t := (hitSet P a n).min' ne
    have member : t ∈ P := (mem_filter.mp ((hitSet P a n).min'_mem ne)).1
    calc
      _ = ∑ p ∈ P, (if p=t then 1 else 0) := by
        apply sum_congr rfl
        intro p hp
        have eq := first_iff S P a hn hp ne
        simp only [firstRow,mem_filter,hn,true_and] at eq
        by_cases same : p=t
        · rw [if_pos same,if_pos (eq.mpr same)]
        · rw [if_neg same,if_neg (fun hit => same (eq.mp hit))]
      _ = _ := by simp [member]
  · rw [if_neg ne]
    apply sum_eq_zero
    intro p hp
    exact if_neg (fun yes => ne ⟨p,mem_filter.mpr ⟨hp,yes.1⟩⟩)

theorem pair_count (S P : Finset ℕ) (a : ℕ → ℕ) :
    (∑ p ∈ P, ∑ n ∈ firstRow S P a p, ((hitSet P a n).filter (fun q => p<q)).card) =
      ∑ n ∈ S, (multiplicity P a n-1) := by
  classical
  simp only [firstRow,Finset.sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  let K := hitSet P a n
  change _ = K.card-1
  by_cases ne : K.Nonempty
  · let t := K.min' ne
    have tm : t ∈ K := K.min'_mem ne
    have tp : t ∈ P := (mem_filter.mp tm).1
    have only : K.filter (fun q => t<q)=K.erase t := by
      ext q
      rw [mem_filter,mem_erase]
      exact ⟨fun h => ⟨h.2.ne',h.1⟩,fun h => ⟨h.2,lt_of_le_of_ne (K.min'_le _ h.2) h.1.symm⟩⟩
    rw [← Finset.card_erase_of_mem tm,← only]
    let f := fun p => if n%p=a p%p ∧ ∀ r ∈ P, r<p → n%r ≠ a r%r
      then (K.filter (fun q => p<q)).card else 0
    change (∑ p ∈ P, f p) = _
    calc
      _ = f t := by
        apply sum_eq_single t
        · intro p hp diff
          have eq := first_iff S P a hn hp ne
          simp only [firstRow,mem_filter,hn,true_and] at eq
          exact if_neg (fun yes => diff (eq.mp yes))
        · intro bad; exact (bad tp).elim
      _ = _ := if_pos (by simpa only [firstRow,mem_filter,hn,true_and] using
        (first_iff S P a hn tp ne).mpr rfl)
  · have empty := Finset.not_nonempty_iff_eq_empty.mp ne
    rw [empty,card_empty,Nat.zero_sub]
    apply sum_eq_zero
    intro p hp
    exact if_neg (fun yes => ne ⟨p,mem_filter.mpr ⟨hp,yes.1⟩⟩)

end PremierRecouvrant687
#print axioms PremierRecouvrant687.first_count
#print axioms PremierRecouvrant687.pair_count
