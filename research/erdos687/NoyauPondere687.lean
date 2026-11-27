import PolynomePoids687
import VerificationPoids687

namespace NoyauPondere687
open PolynomePoids687

export VerificationPoids687 (B half ceiling phase rowCheck check)

def Obstruction (L N : ℕ) (primes : List ℕ) : Prop :=
  ∀ r : ℕ → ℕ, (∀ p ∈ primes, p≤17 → r p%p=phase L p) →
    ¬∀ i<N, ∃ p ∈ primes, i%p=r p%p

private theorem transpose (N : ℕ) (w r : ℕ → ℕ) (rows : List (ℕ × ℕ)) :
    (∑ i ∈ Finset.range N,
      (rows.map (fun q => if i%q.1=r q.1%q.1 then w i else 0)).sum) =
    (rows.map (fun q => row N w q.1 (r q.1%q.1))).sum := by
  induction rows with
  | nil => simp
  | cons q qs ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih,row]

private theorem covered_weight (i : ℕ) (w r : ℕ → ℕ) (rows : List (ℕ × ℕ))
    (hit : ∃ p ∈ rows.map Prod.fst, i%p=r p%p) :
    w i ≤ (rows.map (fun q => if i%q.1=r q.1%q.1 then w i else 0)).sum := by
  induction rows with
  | nil => simp at hit
  | cons q qs ih =>
    simp only [List.map_cons,List.sum_cons]
    by_cases eqn : i%q.1=r q.1%q.1
    · simp [eqn]
    · obtain ⟨p,hp,h⟩ := hit
      rcases List.mem_cons.mp hp with hp|hp
      · exact (eqn (hp ▸ h)).elim
      · simpa [eqn] using ih ⟨p,hp,h⟩

theorem sound {F L N : ℕ} {rows : List (ℕ × ℕ)} (test : check F L N rows=true) :
    Obstruction L N (rows.map Prod.fst) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at test
  obtain ⟨⟨size,limit,mask,gap⟩,tests⟩ := test
  intro r normalized all
  let w := digit B F
  have ceilingMass : half ≤ B-1 := by decide
  have mass := total_from_word (bits := 32) rfl (by decide : 1<B)
    (by decide : ceiling<B) size (limit.trans_le ceilingMass) mask
  have small : (∑ i ∈ Finset.range N, w i)<half :=
    (input_bound (bits := 32) rfl (by decide : 1<B) (by decide : ceiling<B) mask).trans_lt limit
  have upper (q : ℕ × ℕ) (hq : q ∈ rows) : row N w q.1 (r q.1%q.1) ≤ q.2 := by
    have t := tests q hq
    by_cases old : q.1≤17
    · simp only [rowCheck,if_pos old,decide_eq_true_eq] at t
      rw [show row N w q.1 (r q.1%q.1)=_ from fixed_row (by decide : 1<B) t.1 size
        (small.trans_le ceilingMass) (r q.1),
        normalized q.1 (List.mem_map.mpr ⟨q,hq,rfl⟩) old]
      change VerificationPoids687.digit B _ _ ≤ _
      rw [t.2]
      exact Nat.zero_le _
    · simp only [rowCheck,if_neg old,decide_eq_true_eq] at t
      have pp : 0<q.1 := by omega
      exact packed_cap (bits := 32) rfl (by decide : 1<B) (by decide : B=2*half)
        pp w (pack_digit (by decide : 0<B) size) small t.1 t.2 (Nat.mod_lt _ pp)
  have bound : (rows.map (fun q => row N w q.1 (r q.1%q.1))).sum ≤ (rows.map Prod.snd).sum := by
    clear tests gap normalized all
    induction rows with
    | nil => simp
    | cons q qs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add (upper q (by simp)) (ih (fun a ha => upper a (by simp [ha])))
  have lower := Finset.sum_le_sum (s := Finset.range N)
    (fun i hi => covered_weight i w r rows (all i (Finset.mem_range.mp hi)))
  rw [transpose] at lower
  exact (Nat.not_lt_of_ge (lower.trans bound)) (mass.symm ▸ gap)

theorem encoded {L N : ℕ} {ps : List ℕ} (h : VerificationPoids687.Encoded L N ps) :
    Obstruction L N ps := by
  obtain ⟨F,rows,rfl,ok⟩ := h
  exact sound (F := F) ok

end NoyauPondere687
