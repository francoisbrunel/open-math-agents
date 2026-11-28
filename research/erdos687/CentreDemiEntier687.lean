import DilatationCarree687

/-! Rational alignment at an odd half-integer. Reflection gives exactly
one candidate of either parity for each sufficiently small odd prime. -/
namespace CentreDemiEntier687
open Filter Transfert687

theorem stock {z H h b : ℕ} (hz : 2 ≤ z) (odd : b%2=1)
    (left : h+2 ≤ b) (right : b+h ≤ 2*H) (a : ℕ → ℕ)
    (align : ∀ p ∈ z.primesLE, p ≠ 2 → 2*a p ≡ b [MOD p]) :
    (h.primesLE \ z.primesLE).card ≤ (survivors z H a).card := by
  let Q := h.primesLE \ z.primesLE
  let f (q : ℕ) := if ((b+q)/2)%2=a 2%2 then (b-q)/2 else (b+q)/2
  have facts (q : ℕ) (hq : q ∈ Q) :
      z < q ∧ q ≤ h ∧ q.Prime ∧ 2 ≤ 2*f q ∧ 2*f q ≤ 2*H ∧
      f q%2 ≠ a 2%2 ∧ (2*f q+q=b ∨ 2*f q=b+q) := by
    obtain ⟨pos,excl⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨qh,pr⟩ := Nat.mem_primesLE.mp pos
    have large : z < q := lt_of_not_ge (fun le => excl (Nat.mem_primesLE.mpr ⟨le,pr⟩))
    have qo := pr.eq_two_or_odd.resolve_left (by omega)
    refine ⟨large,qh,pr,?_⟩
    dsimp only [f]
    split <;> omega
  apply Finset.card_le_card_of_injOn f
  · intro q hq
    obtain ⟨big,_,pr,lo,up,parity,sign⟩ := facts q hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    intro p hp hit
    by_cases two : p=2
    · subst p; exact parity hit
    have eq : 2*f q ≡ b [MOD p] := (Nat.ModEq.mul_left 2 hit).trans (align p hp two)
    have dv : p ∣ q := by
      rcases sign with neg|pos
      · simpa only [← neg,Nat.add_sub_cancel_left] using eq.dvd'
      · simpa only [pos,Nat.add_sub_cancel_left] using eq.symm.dvd'
    obtain ⟨pz,pp⟩ := Nat.mem_primesLE.mp hp
    rcases (Nat.dvd_prime pr).mp dv with unit|same
    · exact pp.ne_one unit
    · omega
  · intro i hi j hj eq
    obtain ⟨_,_,_,_,_,_,si⟩ := facts i hi
    obtain ⟨_,_,_,_,_,_,sj⟩ := facts j hj
    change f i=f j at eq
    omega

theorem square {z b : ℕ} (hz : 512 ≤ z) (odd : b%2=1)
    (left : z^2/2+2 ≤ b) (right : b+z^2/2 ≤ 2*z^2) (a : ℕ → ℕ)
    (align : ∀ p ∈ z.primesLE, p ≠ 2 → 2*a p ≡ b [MOD p]) :
    (z:ℝ)^2/(64*Real.log z) ≤ ((survivors z (z^2) a).card:ℝ) := by
  have supply := DilatationCarree687.prime_distances (D := 1) (by decide) (by simpa using hz)
  have hits := stock (z := z) (by omega) odd left right a align
  apply le_trans _ (Nat.cast_le.mpr hits)
  simpa only [Nat.mul_one,Nat.cast_one,one_mul] using supply

/-- A common odd numerator for all odd rows forbids a full cover as soon
as both sides of the half-integer have room for a prime in (x,2x]. -/
theorem no_full_cover {x H b : ℕ} (hx : 2 ≤ x) (odd : b%2=1)
    (left : 2*x+2 ≤ b) (right : b+2*x ≤ 2*H) (a : ℕ → ℕ)
    (align : ∀ p ∈ x.primesLE, p ≠ 2 → 2*a p ≡ b [MOD p]) :
    ¬ (∀ n ∈ Finset.Icc 1 H, ∃ p ≤ x, p.Prime ∧ n%p=a p%p) := by
  intro cover
  obtain ⟨q,pr,large,small⟩ := Nat.exists_prime_lt_and_le_two_mul x (by omega)
  have mem : q ∈ (2*x).primesLE \ x.primesLE :=
    Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨small,pr⟩,
      fun h => large.not_ge (Nat.mem_primesLE.mp h).1⟩
  obtain ⟨n,hn⟩ := Finset.card_pos.mp ((Finset.card_pos.mpr ⟨q,mem⟩).trans_le
    (stock hx odd left right a align))
  obtain ⟨interval,avoid⟩ := Finset.mem_filter.mp hn
  obtain ⟨p,px,pp,hit⟩ := cover n interval
  exact avoid p (Nat.mem_primesLE.mpr ⟨px,pp⟩) hit

end CentreDemiEntier687
#print axioms CentreDemiEntier687.stock
#print axioms CentreDemiEntier687.square
#print axioms CentreDemiEntier687.no_full_cover
