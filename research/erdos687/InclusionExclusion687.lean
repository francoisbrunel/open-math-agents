import Transfert687
import Mathlib.Data.Nat.ModEq

/-! A third-order deletion test for arbitrary residues. Pair overlaps can
    compensate for a first-order union estimate that already exceeds the stock. -/
namespace Recouvrements687
open Transfert687

def hits (P : Finset ℕ) (a : ℕ → ℕ) (n : ℕ) := (P.filter fun p => n%p = a p%p).card

private theorem pointwise (t : ℕ) :
    1+t.choose 2 ≤ (if t=0 then 1 else 0)+t+t.choose 3 := by
  cases t with
  | zero => decide
  | succ k =>
    have h2 : (k+1).choose 2 = k + k.choose 2 := by
      simpa using Nat.choose_succ_succ k 1
    have h3 : (k+1).choose 3 = k.choose 2+k.choose 3 := Nat.choose_succ_succ k 2
    simp only [Nat.succ_ne_zero,if_false,Nat.zero_add]
    omega

/-- Lower Bonferroni bound with all terms in natural numbers. -/
theorem third_order (S : Finset ℕ) (t : ℕ → ℕ) :
    S.card + (∑ n ∈ S, (t n).choose 2) ≤
      (S.filter fun n => t n=0).card + (∑ n ∈ S, t n) + (∑ n ∈ S, (t n).choose 3) := by
  have h := Finset.sum_le_sum (s := S) (fun n _ => pointwise (t n))
  simpa [Finset.sum_add_distrib] using h

/-- Sufficient criterion for an upper bound on the official Y at any
    cutoff z. It uses the number of double and triple hits on the old survivors. -/
theorem upper_from_overlaps {x z N : ℕ}
    (estimate : ∀ a : ℕ → ℕ,
      let S := survivors z N a
      let t := hits (x.primesLE \ z.primesLE) a
      (∑ n ∈ S, t n)+(∑ n ∈ S, (t n).choose 3) < S.card+(∑ n ∈ S, (t n).choose 2)) :
    Erdos687.Y x ≤ N := by
  apply csSup_le
  · exact ⟨0,fun _ => 0,by simp⟩
  · intro y hy
    obtain ⟨a,ha⟩ := hy
    by_contra! large
    let S := survivors z N a
    let P := x.primesLE \ z.primesLE
    let t := hits P a
    have hb := third_order S t
    have he := estimate a
    change (∑ n ∈ S, t n)+(∑ n ∈ S, (t n).choose 3) < S.card+(∑ n ∈ S, (t n).choose 2) at he
    have hn : 0 < (S.filter fun n => t n=0).card := by omega
    obtain ⟨n,hn⟩ := Finset.card_pos.mp hn
    obtain ⟨hS,none⟩ := Finset.mem_filter.mp hn
    obtain ⟨hI,avoid⟩ := Finset.mem_filter.mp hS
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hI
    obtain ⟨p,hpx,prime,equal⟩ := ha n (Finset.mem_Icc.mpr ⟨lo,hi.trans large.le⟩)
    have pin : p ∈ P := Finset.mem_sdiff.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hpx,prime⟩,fun hp => avoid p hp equal⟩
    have yes : p ∈ P.filter (fun q => n%q = a q%q) := Finset.mem_filter.mpr ⟨pin,equal⟩
    exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨p,yes⟩)) none

/-- Below the product of two coprime moduli a prescribed pair of classes
    meets the interval in at most one point, uniformly over the residues. -/
theorem pair_capacity {p q N : ℕ} (cop : p.Coprime q) (short : N < p*q) (a : ℕ → ℕ) :
    ((Finset.Icc 1 N).filter fun n => n%p = a p%p ∧ n%q = a q%q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiI,hip,hiq⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjI,hjp,hjq⟩ := Finset.mem_filter.mp hj
  have both : i ≡ j [MOD p*q] := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
    ⟨hip.trans hjp.symm,hiq.trans hjq.symm⟩
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt ((Finset.mem_Icc.mp hiI).2.trans_lt short),
    Nat.mod_eq_of_lt ((Finset.mem_Icc.mp hjI).2.trans_lt short)] using both

end Recouvrements687
