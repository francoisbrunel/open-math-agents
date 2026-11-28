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

theorem positive_support {F L N : ℕ} {rows : List (ℕ × ℕ)} (test : check F L N rows=true)
    (r : ℕ → ℕ) (normalized : ∀ p ∈ rows.map Prod.fst, p≤17 → r p%p=phase L p)
    (all : ∀ i<N, 0 < digit B F i → ∃ p ∈ rows.map Prod.fst, i%p=r p%p) : False := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at test
  obtain ⟨⟨size,limit,mask,gap⟩,tests⟩ := test
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
  have lower : (∑ i ∈ Finset.range N, w i) ≤
      ∑ i ∈ Finset.range N, (rows.map (fun q => if i%q.1=r q.1%q.1 then w i else 0)).sum := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : 0 < w i
    · exact covered_weight i w r rows (all i (Finset.mem_range.mp hi) h)
    · simp [Nat.eq_zero_of_not_pos h]
  rw [transpose] at lower
  exact (Nat.not_lt_of_ge (lower.trans bound)) (mass.symm ▸ gap)

theorem sound {F L N : ℕ} {rows : List (ℕ × ℕ)} (test : check F L N rows=true) :
    Obstruction L N (rows.map Prod.fst) := by
  intro r norm all
  exact positive_support test r norm (fun i hi _ => all i hi)

/-- For each residue of a new prime, certify the positive support on the
    other rows and verify that its mass on the prescribed residue is zero. -/
theorem branch {L N p : ℕ} {ps : List ℕ} (prime_pos : 0 < p)
    (cases : ∀ j : Fin p, ∃ F rows, rows.map Prod.fst = ps ∧ check F L N rows = true ∧
      digit B (F % (B^p-1)) j.val = 0) : Obstruction L N (p :: ps) := by
  intro r norm all
  let j : Fin p := ⟨r p % p,Nat.mod_lt _ prime_pos⟩
  obtain ⟨F,rows,list,test,zero⟩ := cases j
  have h := test
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨size,limit,mask,_⟩,_⟩ := h
  have light := (input_bound (bits := 32) rfl (by decide : 1<B) (by decide : ceiling<B) mask).trans_lt
    (limit.trans_le (by decide : half ≤ B-1))
  have empty : row N (digit B F) p (r p%p) = 0 :=
    (fixed_row (by decide : 1<B) prime_pos size light (r p)).trans zero
  apply positive_support test r
  · intro q hq small
    exact norm q (List.mem_cons_of_mem p (list ▸ hq)) small
  · intro i hi positive
    obtain ⟨q,hq,hit⟩ := all i hi
    rcases List.mem_cons.mp hq with eq | rest
    · subst q
      have one := Finset.single_le_sum (f := fun n : ℕ => if n%p=r p%p then digit B F n else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
      change _ ≤ row N (digit B F) p (r p%p) at one
      rw [empty,if_pos hit] at one
      omega
    · exact ⟨q,list.symm ▸ rest,hit⟩

theorem encoded {L N : ℕ} {ps : List ℕ} (h : VerificationPoids687.Encoded L N ps) :
    Obstruction L N ps := by
  obtain ⟨F,rows,rfl,ok⟩ := h
  exact sound (F := F) ok

end NoyauPondere687
