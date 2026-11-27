import ReductionIwaniec
import Couvertures687
import Exclusion687
import Comptage687

/-! The module ReductionIwaniec is the unchanged submission file, replayed under
    a simple local module name. See REPLAY.txt for the build commands. -/
namespace Transfert687

open Couvertures687 Filter
open scoped BigOperators Asymptotics
open OMA.R_Erdos687_erdos_687_variants_iwaniec_R2

theorem covered_of_rows {x N : ℕ} (s : Classes) (empty : holes s N = [])
    (valid : ∀ t ∈ s, t.1 ≤ x ∧ Nat.Prime t.1 ∧ t.2 = (s.lookup t.1).getD 0 % t.1) :
    Green46.IsCoveredByResidues x N := by
  refine ⟨fun p => (s.lookup p).getD 0, ?_⟩
  intro n hn
  obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp hn
  have hh := hits_of_no_holes empty (n := n) (by omega) hi
  obtain ⟨⟨p,r⟩, hpr, hhit⟩ := List.any_eq_true.mp hh
  obtain ⟨hp, hprime, hr⟩ := valid (p,r) hpr
  have hn : n % p = r := by simpa using hhit
  exact ⟨p, hp, hprime, hn.trans hr⟩

theorem le_Y_of_covered {x N : ℕ} (h : Green46.IsCoveredByResidues x N) : N ≤ Erdos687.Y x :=
  le_csSup (show BddAbove {y | Green46.IsCoveredByResidues x y} from
    ⟨primorial x, fun _ hy => (Erdos687.lt_primorial_of_isCoveredByResidues hy).le⟩) h

theorem Y47_lower : 99 ≤ Erdos687.Y 47 :=
  le_Y_of_covered (covered_of_rows at47 witness47 (by decide))

theorem Y73_lower : 189 ≤ Erdos687.Y 73 :=
  le_Y_of_covered (covered_of_rows at73 witness73 (by decide))

/-- If a finite protected set uses fewer than r residues, one residue misses every point. -/
theorem avoids_of_card_lt (T : Finset ℕ) {r : ℕ} (h : T.card < r) :
    ∃ a < r, ∀ n ∈ T, n % r ≠ a := by
  by_contra! hn
  have subset : Finset.range r ⊆ T.image (· % r) := by
    intro a ha
    obtain ⟨n, hT, he⟩ := hn a (Finset.mem_range.mp ha)
    exact Finset.mem_image.mpr ⟨n, hT, he⟩
  have bad := (Finset.card_le_card subset).trans Finset.card_image_le
  simp at bad
  omega

/-- Small primes use zero, larger ones use a residue outside the protected set. -/
theorem simultaneous_protection (T : Finset ℕ) {u z : ℕ} (size : T.card ≤ u)
    (rough : ∀ r ∈ u.primesLE, ∀ n ∈ T, n % r ≠ 0) :
    ∃ a : ℕ → ℕ, ∀ r ∈ z.primesLE, ∀ n ∈ T, n % r ≠ a r := by
  classical
  let a (r : ℕ) := if h : u < r then
      Classical.choose (avoids_of_card_lt T (size.trans_lt h)) else 0
  refine ⟨a, ?_⟩
  intro r hr n hn
  by_cases h : u < r
  · simpa [a, h] using (Classical.choose_spec (avoids_of_card_lt T (size.trans_lt h))).2 n hn
  · simpa [a, h] using rough r (Nat.mem_primesLE.mpr
      ⟨Nat.le_of_not_gt h, (Nat.mem_primesLE.mp hr).2⟩) n hn

def survivors (x N : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∀ p ∈ x.primesLE, n % p ≠ a p % p

def charge (S : Finset ℕ) (a : ℕ → ℕ) (p : ℕ) : ℕ :=
  (S.filter fun n => n % p = a p % p).card

/-- The parity left by 2 is an arithmetic progression of step 2.
    Pull any odd-prime residue back to at most one residue of its index. -/
theorem parity_transfer {z L k : ℕ} (ps : List ℕ)
    (oddPrimes : ∀ p ∈ z.primesLE, p ≠ 2 → p ∈ ps ∧ Nat.gcd p 2 = 1)
    (reject : ∀ b : ℕ → ℕ, k < (Exclusion687.left b ps (List.range L)).length)
    (a : ℕ → ℕ) : k < (survivors z (2*L) a).card := by
  classical
  let t := if a 2 % 2 = 0 then 1 else 2
  let f := fun i : ℕ => 2*i+t
  let b (p : ℕ) := if h : ∃ i, f i % p = a p % p then Classical.choose h else 0
  let live := Exclusion687.left b ps (List.range L)
  have nd : live.Nodup := (Exclusion687.left_sublist b ps (List.range L)).nodup List.nodup_range
  have incl : live.toFinset.image f ⊆ survivors z (2*L) a := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hiL, avoid⟩ := (Exclusion687.mem_left _ _ _ _).mp (List.mem_toFinset.mp hi)
    have hi' := List.mem_range.mp hiL
    have ht : t = 1 ∨ t = 2 := by by_cases h : a 2 % 2 = 0 <;> simp [t,h]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · dsimp [f]; omega
    · dsimp [f]; omega
    · intro p hp eqn
      by_cases h2 : p = 2
      · subst p
        dsimp [f,t] at eqn
        split at eqn <;> omega
      · obtain ⟨hps, hg⟩ := oddPrimes p hp h2
        have ex : ∃ j, f j % p = a p % p := ⟨i,eqn⟩
        have he : f i ≡ f (b p) [MOD p] := by
          change f i % p = f (b p) % p
          rw [eqn]
          simpa [b, ex] using (Classical.choose_spec ex).symm
        exact avoid p hps (Nat.ModEq.cancel_left_of_coprime hg (Nat.ModEq.add_right_cancel' t he))
  have inj : Function.Injective f := by intro i j h; dsimp [f] at h; omega
  have count := Finset.card_le_card incl
  rw [Finset.card_image_of_injective _ inj, List.toFinset_card_of_nodup nd] at count
  exact (reject b).trans_le count

theorem nine_survivors_through23 (a : ℕ → ℕ) : 8 < (survivors 23 96 a).card :=
  parity_transfer (L := 48) [3,5,7,11,13,17,19,23]
    (by decide) Exclusion687.eight_holes_impossible_23 a

theorem one_survivor_through37 (a : ℕ → ℕ) : 0 < (survivors 37 66 a).card :=
  parity_transfer (L := 33) [3,5,7,11,13,17,19,23,29,31,37]
    (by decide) Exclusion687.impossible_37 a

/-- Exact value with the interval convention in Formal Conjectures. -/
theorem Y37_exact : Erdos687.Y 37 = 65 := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, fun _ => 0, by simp⟩
    · rintro y ⟨a, ha⟩
      by_contra! hy
      obtain ⟨n, hn⟩ := Finset.card_pos.mp (one_survivor_through37 a)
      obtain ⟨hi, avoid⟩ := Finset.mem_filter.mp hn
      obtain ⟨lo, top⟩ := Finset.mem_Icc.mp hi
      obtain ⟨p, hp, prime, eqn⟩ := ha n (Finset.mem_Icc.mpr ⟨lo, by omega⟩)
      exact avoid p (Nat.mem_primesLE.mpr ⟨hp,prime⟩) eqn
  · let rows : Classes := [(2,1),(3,2),(5,4),(7,2),(11,7),(13,10),
        (17,12),(19,3),(23,6),(29,28),(31,11),(37,11)]
    exact le_Y_of_covered (covered_of_rows rows (by decide) (by decide))

/-- Any two distinct points escaping through 71 in a 73-cover of [1,189]
    differ by exactly 146. The exhaustive Python result is needed only to
    show that two such points always exist; this implication is unconditional. -/
theorem mandatory_distance {a : ℕ → ℕ}
    (cover : ∀ n ∈ Finset.Icc 1 189, ∃ p ≤ 73, Nat.Prime p ∧ n % p = a p % p)
    {i j : ℕ} (hi : i ∈ survivors 71 189 a) (hj : j ∈ survivors 71 189 a)
    (hij : i < j) : j = i + 146 := by
  have residue {n : ℕ} (hn : n ∈ survivors 71 189 a) :
      n % 73 = a 73 % 73 ∧ n % 2 ≠ a 2 % 2 ∧ 1 ≤ n ∧ n ≤ 189 := by
    obtain ⟨hnI, hs⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, hpx, hp, he⟩ := cover n hnI
    have hlarge : 71 < p := by
      by_contra! h
      exact hs p (Nat.mem_primesLE.mpr ⟨h, hp⟩) he
    have h73 : p = 73 := by
      interval_cases p <;> first | rfl | exact False.elim ((by decide : ¬ Nat.Prime 72) hp)
    subst p
    exact ⟨he, hs 2 (by decide), Finset.mem_Icc.mp hnI⟩
  obtain ⟨hi73, hi2, hil, hiu⟩ := residue hi
  obtain ⟨hj73, hj2, hjl, hju⟩ := residue hj
  omega

/-- Partition an interval into complete blocks. If at least s survivors
    occur per block, k exceptional points bound the interval length.
    Counting the complete blocks separately supplies the premise. -/
theorem block_length {N B k s : ℕ} (hB : 0 < B) (hs : 0 < s)
    (count : (N / B) * s ≤ k) : N < (k / s + 1) * B := by
  have hdiv : N / B ≤ k / s := (Nat.le_div_iff_mul_le hs).mpr count
  have hn : N / B < k / s + 1 := by omega
  exact (Nat.div_lt_iff_lt_mul hB).mp hn

/-- Counting the assigned survivors forces a large prime to cover several. -/
theorem some_large_class {x z N k : ℕ} {a : ℕ → ℕ}
    (cov : ∀ n ∈ Finset.Icc 1 N, ∃ p ≤ x, Nat.Prime p ∧ n % p = a p % p)
    (many : (x.primesLE \ z.primesLE).card * k < (survivors z N a).card) :
    ∃ p ∈ x.primesLE \ z.primesLE, k < charge (survivors z N a) a p := by
  by_contra! h
  have summed := Finset.sum_le_sum h
  have total := survivor_le_sum (z := z) a cov
  change (survivors z N a).card ≤
    ∑ p ∈ x.primesLE \ z.primesLE, charge (survivors z N a) a p at total
  have bound : (survivors z N a).card ≤ (x.primesLE \ z.primesLE).card * k := by
    simpa using total.trans summed
  omega

/-- A fractional double cover obstructs every nonnegative additive certificate.
    The two incidence indicators may coincide for the same prime. -/
theorem double_cover_obstruction {ι α : Type*} [DecidableEq α]
    (P : Finset ι) (S : Finset α) (A B : ι → Finset α) (w : α → ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n)
    (twice : ∀ n ∈ S, (2 : ℝ) ≤ ∑ p ∈ P,
      ((if n ∈ A p then (1 : ℝ) else 0) + (if n ∈ B p then 1 else 0))) :
    (∑ n ∈ S, w n) ≤ ∑ p ∈ P, max
      (∑ n ∈ S, w n * (if n ∈ A p then 1 else 0))
      (∑ n ∈ S, w n * (if n ∈ B p then 1 else 0)) := by
  let a (p : ι) (n : α) : ℝ := if n ∈ A p then 1 else 0
  let b (p : ι) (n : α) : ℝ := if n ∈ B p then 1 else 0
  have h1 : ∑ n ∈ S, w n * 2 ≤
      ∑ n ∈ S, ∑ p ∈ P, (w n * a p n + w n * b p n) := by
    apply Finset.sum_le_sum
    intro n hn
    simpa [Finset.mul_sum, mul_add, a, b] using
      mul_le_mul_of_nonneg_left (twice n hn) (hw n hn)
  rw [Finset.sum_comm] at h1
  have h2 : (∑ p ∈ P, ∑ n ∈ S, (w n * a p n + w n * b p n)) ≤
      ∑ p ∈ P, max (∑ n ∈ S, w n * a p n) (∑ n ∈ S, w n * b p n) * 2 := by
    apply Finset.sum_le_sum
    intro p _
    rw [Finset.sum_add_distrib, mul_two]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have hh := h1.trans h2
  simp only [← Finset.sum_mul] at hh
  exact (le_of_mul_le_mul_right hh (by norm_num : (0 : ℝ) < 2))

/-- Propagate the three independent analytic inputs with explicit slack.
    W is the stock normalization, V the per-prime normalization. -/
theorem budget_from_weights {x z N : ℕ} {W V : ℝ} (pos : 0 < W)
    (stock : ∀ a, W / 125 ≤ ((survivors z N a).card : ℝ))
    (progression : ∀ a p, p ∈ x.primesLE \ z.primesLE →
      (charge (survivors z N a) a p : ℝ) ≤ (5/2 : ℝ) * (V / p))
    (harmonic : (∑ p ∈ x.primesLE \ z.primesLE, V / (p : ℝ)) ≤ 3/1000 * W) :
    Erdos687.Y x ≤ N := by
  apply upper_of_survivor_budget (z := z)
  intro a
  change (∑ p ∈ x.primesLE \ z.primesLE, charge (survivors z N a) a p) < (survivors z N a).card
  have hs := Finset.sum_le_sum (fun p hp => progression a p hp)
  rw [← Finset.mul_sum] at hs
  have key : (∑ p ∈ x.primesLE \ z.primesLE, (charge (survivors z N a) a p : ℝ)) <
      ((survivors z N a).card : ℝ) := by linarith [stock a]
  exact_mod_cast key

/-- A uniform progression sieve and a prime-counting bound suffice for
    the second step of the submitted reduction. The numerical slack is 40. -/
theorem H2_from_linear_estimates
    (hpi : ∀ᶠ x : ℕ in atTop, x.primesLE.card ≤ 30 * (x / (x.log2+1)))
    (hprog : ∀ᶠ x : ℕ in atTop, ∀ a p, p ∈ x.primesLE \ (x/2).primesLE →
      charge (survivors (x/2) (x^2) a) a p ≤ 32 * (x / (x.log2+1))) : H2 := by
  filter_upwards [hpi, hprog] with x hcount hclass
  intro a
  let d := x / (x.log2+1)
  let band := x.primesLE \ (x/2).primesLE
  change (∑ p ∈ band, charge (survivors (x/2) (x^2) a) a p) ≤ 1000*d^2
  have hb : band.card ≤ 30*d := (Finset.card_le_card Finset.sdiff_subset).trans hcount
  calc
    _ ≤ ∑ _p ∈ band, 32*d := Finset.sum_le_sum (hclass a)
    _ = band.card * (32*d) := by simp
    _ ≤ (30*d)*(32*d) := Nat.mul_le_mul_right _ hb
    _ ≤ 1000*d^2 := by nlinarith [Nat.zero_le (d^2)]

theorem H2_from_progression
    (hprog : ∀ᶠ x : ℕ in atTop, ∀ a p, p ∈ x.primesLE \ (x/2).primesLE →
      charge (survivors (x/2) (x^2) a) a p ≤ 32 * (x / (x.log2+1))) : H2 :=
  H2_from_linear_estimates Comptage687.normalized_prime_count hprog

/-- The analytic estimates are hypotheses, including conversion of the chosen
    integer length to the explicit real scale. No sieve theorem is postulated. -/
theorem log_saving_of_inputs (N z : ℕ → ℕ) (W V : ℕ → ℝ)
    (pos : ∀ᶠ x in atTop, 0 < W x)
    (stock : ∀ᶠ x in atTop, ∀ a, W x / 125 ≤ ((survivors (z x) (N x) a).card : ℝ))
    (progression : ∀ᶠ x in atTop, ∀ a p, p ∈ x.primesLE \ (z x).primesLE →
      (charge (survivors (z x) (N x) a) a p : ℝ) ≤ (5/2 : ℝ) * (V x / p))
    (harmonic : ∀ᶠ x in atTop,
      (∑ p ∈ x.primesLE \ (z x).primesLE, V x / (p : ℝ)) ≤ 3/1000 * W x)
    (scale : (fun x => (N x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ)^2 / (Real.log x) ^ (401/200 : ℝ))) :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ)^2 / (Real.log x) ^ (401/200 : ℝ)) := by
  apply Asymptotics.IsBigO.trans _ scale
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [pos, stock, progression, harmonic] with x hp hs hq hh
  have h := budget_from_weights hp hs hq hh
  simpa using (show (Erdos687.Y x : ℝ) ≤ (N x : ℝ) by exact_mod_cast h)

noncomputable def cutoff (x : ℕ) : ℝ := (x : ℝ) / (Real.log x) ^ (1/400 : ℝ)

noncomputable def blockLength (x : ℕ) : ℕ :=
  ⌊(cutoff x)^2 / (Real.log (cutoff x))^2⌋₊

/-- The choice delta = 1/400 gives the exponent 401/200 even after flooring
    the block length. This part of the scale conversion is unconditional. -/
theorem explicit_block_scale :
    (fun x => (blockLength x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ)^2 / (Real.log x) ^ (401/200 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
  have hx' : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  let L := Real.log (x : ℝ)
  have hL : 0 < L := Real.log_pos hx'
  have hD : 0 < L ^ (1/400 : ℝ) := Real.rpow_pos_of_pos hL _
  have logz : Real.log (cutoff x) = L - 1/400 * Real.log L := by
    rw [cutoff, Real.log_div (by positivity) hD.ne', Real.log_rpow hL]
  have lower : L / 2 ≤ Real.log (cutoff x) := by
    rw [logz]
    linarith [Real.log_le_sub_one_of_pos hL]
  have expand : L ^ (401/200 : ℝ) = (L ^ (1/400 : ℝ))^2 * L^2 := by
    rw [show (401/200 : ℝ) = (1/400 : ℝ) * 2 + 2 by norm_num,
      Real.rpow_add hL, Real.rpow_mul hL.le]
    norm_num
  have hf : (blockLength x : ℝ) ≤ (cutoff x)^2 / (Real.log (cutoff x))^2 :=
    Nat.floor_le (by positivity)
  have h := calc
    (blockLength x : ℝ) ≤ (cutoff x)^2 / (Real.log (cutoff x))^2 := hf
    _ ≤ (cutoff x)^2 / (L/2)^2 := by gcongr
    _ = 4 * ((x : ℝ)^2 / L^(401/200 : ℝ)) := by
      rw [expand]
      change ((x : ℝ) / L ^ (1/400 : ℝ))^2 / (L/2)^2 = _
      field_simp
      ring
  change ‖(blockLength x : ℝ)‖ ≤ 4 * ‖(x : ℝ)^2 / L ^ (401/200 : ℝ)‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (blockLength x : ℝ) by positivity),
    abs_of_nonneg (show (0 : ℝ) ≤ (x : ℝ)^2 / L ^ (401/200 : ℝ) by positivity)] using h

end Transfert687
