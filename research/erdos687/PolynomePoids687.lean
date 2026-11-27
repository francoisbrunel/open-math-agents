import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Kronecker encoding of a weighted interval. Reducing the encoded number
    modulo B^p-1 adds the weights in each congruence class modulo p. -/
namespace PolynomePoids687

def pack (B N : ℕ) (w : ℕ → ℕ) := ∑ i ∈ Finset.range N, w i*B^i
def digit (B F i : ℕ) := F/B^i%B
def ones (B n : ℕ) := (B^n-1)/(B-1)
def row (N : ℕ) (w : ℕ → ℕ) (p r : ℕ) :=
  ∑ i ∈ Finset.range N, if i%p=r then w i else 0

theorem head (B n : ℕ) (w : ℕ → ℕ) :
    pack B (n+1) w = w 0 + B*pack B n (fun i => w (i+1)) := by
  simp only [pack,Finset.sum_range_succ',pow_zero,mul_one,Finset.mul_sum,pow_succ]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem digit_pack {B n : ℕ} (pos : 0 < B) (w : ℕ → ℕ)
    (small : ∀ i < n, w i < B) {r : ℕ} (hr : r<n) :
    digit B (pack B n w) r = w r := by
  induction r generalizing w n with
  | zero =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simp only [digit,pow_zero,Nat.div_one,head,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (small 0 (by omega))]
  | succ r ih =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    have h0 := small 0 (by omega)
    rw [digit,pow_succ',← Nat.div_div_eq_div_mul,head,Nat.add_mul_div_left _ _ pos,
      Nat.div_eq_of_lt h0,Nat.zero_add]
    exact ih (fun i => w (i+1)) (fun i hi => small (i+1) (by omega)) (by omega)

theorem pack_digit {B F n : ℕ} (pos : 0 < B) (bounded : F < B^n) :
    pack B n (digit B F) = F := by
  induction n generalizing F with
  | zero => simp only [pow_zero] at bounded; simp [pack,show F=0 by omega]
  | succ n ih =>
    have div : F/B < B^n := (Nat.div_lt_iff_lt_mul pos).mpr (by simpa [pow_succ] using bounded)
    have shift (i : ℕ) : digit B F (i+1) = digit B (F/B) i := by
      simp only [digit,pow_succ',Nat.div_div_eq_div_mul]
    rw [head,show (fun i => digit B F (i+1)) = digit B (F/B) by funext i; exact shift i,ih div]
    simpa [digit] using Nat.mod_add_div F B

theorem ones_eq {B : ℕ} (large : 1<B) (n : ℕ) :
    ones B n = ∑ i ∈ Finset.range n, B^i := by
  rw [ones,← geom_sum_mul_of_one_le large.le,Nat.mul_div_cancel _ (by omega : 0<B-1)]

theorem constant_pack {B : ℕ} (large : 1<B) (n c : ℕ) :
    pack B n (fun _ => c) = c*ones B n := by rw [ones_eq large]; simp [pack,Finset.mul_sum]

theorem add_pack (B n : ℕ) (f g : ℕ → ℕ) :
    pack B n (fun i => f i+g i) = pack B n f+pack B n g := by simp [pack,add_mul,Finset.sum_add_distrib]

theorem row_le (N p r : ℕ) (w : ℕ → ℕ) : row N w p r ≤ ∑ i ∈ Finset.range N, w i := by
  apply Finset.sum_le_sum
  intro i hi
  split <;> omega

private theorem cycle {B p : ℕ} (large : 1<B) (pp : 0<p) (i : ℕ) :
    B^i ≡ B^(i%p) [MOD B^p-1] := by
  have positive : 1 ≤ B^p := Nat.one_le_pow _ _ (by omega)
  have unit : B^p ≡ 1 [MOD B^p-1] := ((Nat.modEq_iff_dvd' positive).mpr dvd_rfl).symm
  calc
    B^i = B^(i%p+p*(i/p)) := by rw [Nat.mod_add_div]
    _ = B^(i%p)*(B^p)^(i/p) := by rw [pow_add,pow_mul]
    _ ≡ B^(i%p)*1^(i/p) [MOD B^p-1] := (unit.pow (i/p)).mul_left _
    _ = B^(i%p) := by simp

theorem folded {B p N : ℕ} (large : 1<B) (pp : 0<p) (w : ℕ → ℕ)
    (light : (∑ i ∈ Finset.range N,w i) < B-1) :
    pack B N w % (B^p-1) = pack B p (row N w p) := by
  let W := ∑ i ∈ Finset.range N,w i
  have rearrange : pack B p (row N w p) = ∑ i ∈ Finset.range N, w i*B^(i%p) := by
    simp only [pack,row,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [ite_mul,Finset.mem_range.mpr (Nat.mod_lt i pp),eq_comm]
  have cong : pack B N w ≡ pack B p (row N w p) [MOD B^p-1] := by
    rw [rearrange]
    exact Nat.ModEq.sum (fun i _ => (cycle large pp i).mul_left (w i))
  have lim : pack B p (row N w p) ≤ W*ones B p := by
    rw [← constant_pack large]
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.mul_le_mul_right _ (row_le N p i w)
  have up : 0 < ones B p := by
    rw [ones_eq large]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0,Finset.mem_range.mpr pp,by simp⟩
  have bound : W*ones B p < (B-1)*ones B p := Nat.mul_lt_mul_of_pos_right light up
  have endval : (B-1)*ones B p = B^p-1 := by
    rw [ones_eq large,Nat.mul_comm]
    exact geom_sum_mul_of_one_le large.le p
  exact (show pack B N w % (B^p-1) = pack B p (row N w p) % (B^p-1) from cong).trans
    (Nat.mod_eq_of_lt (lim.trans_lt (bound.trans_eq endval)))

theorem mask_digit {bits A mask : ℕ} (ok : A &&& mask = A) (i : ℕ) :
    digit (2^bits) A i ≤ digit (2^bits) mask i := by
  have eq := congrArg (fun u : ℕ => (u >>> (bits*i)) % 2^bits) ok
  simp only [Nat.shiftRight_and_distrib,Nat.and_mod_two_pow] at eq
  unfold digit
  rw [← pow_mul,← Nat.shiftRight_eq_div_pow,← Nat.shiftRight_eq_div_pow]
  exact eq.symm.le.trans Nat.and_le_right

/-- The Boolean mask checks all p inequalities simultaneously. The constants
    B=2^bits and half=B/2 are allowed to be chosen per certificate. -/
theorem packed_cap {bits B half p N F c : ℕ} (hb : B=2^bits) (base : 1<B)
    (halves : B=2*half) (pp : 0<p) (w : ℕ → ℕ) (eval : pack B N w=F)
    (small : (∑ i ∈ Finset.range N,w i)<half) (cs : c<half)
    (mask : (F%(B^p-1)+(half-1-c)*ones B p) &&& ((half-1)*ones B p) =
      F%(B^p-1)+(half-1-c)*ones B p) {r : ℕ} (rp : r<p) :
    row N w p r ≤ c := by
  have weak : (∑ i ∈ Finset.range N,w i)<B-1 := by omega
  have fold : F%(B^p-1) = pack B p (row N w p) := by rw [← eval,folded base pp w weak]
  let pad := half-1-c
  have packed : F%(B^p-1)+pad*ones B p = pack B p (fun j => row N w p j+pad) := by
    rw [fold,← constant_pack base,add_pack]
  have cmp := mask_digit (bits := bits) mask r
  rw [← hb,packed,← constant_pack base] at cmp
  have rowSmall (i : ℕ) (_ : i<p) : row N w p i+pad<B := by
    have := row_le N p i w
    dsimp [pad]; omega
  rw [digit_pack (by omega) _ rowSmall rp,digit_pack (by omega) _ (fun _ _ => by omega) rp] at cmp
  dsimp [pad] at cmp
  omega

theorem input_bound {bits B N F L : ℕ} (hb : B=2^bits) (base : 1<B) (lb : L<B)
    (mask : F &&& (L*ones B N) = F) :
    ∑ i ∈ Finset.range N, digit B F i ≤ N*L := by
  calc
    _ ≤ ∑ _i ∈ Finset.range N, L := by
      apply Finset.sum_le_sum
      intro i hi
      have h := mask_digit (bits := bits) mask i
      rw [← hb,← constant_pack base,digit_pack (by omega) _ (fun _ _ => lb) (Finset.mem_range.mp hi)] at h
      exact h
    _ = _ := by simp

theorem total_from_word {bits B N F L : ℕ} (hb : B=2^bits) (base : 1<B) (lb : L<B)
    (size : F<B^N) (limit : N*L<B-1) (mask : F &&& (L*ones B N) = F) :
    ∑ i ∈ Finset.range N, digit B F i = F%(B-1) := by
  have light := (input_bound hb base lb mask).trans_lt limit
  have h := folded (p := 1) base (by decide) (digit B F) light
  rw [pack_digit (by omega) size] at h
  simpa [pack,row,Nat.mod_one] using h.symm

theorem fixed_row {B p N F : ℕ} (base : 1<B) (pp : 0<p) (size : F<B^N)
    (light : (∑ i ∈ Finset.range N, digit B F i)<B-1) (r : ℕ) :
    row N (digit B F) p (r%p) = digit B (F%(B^p-1)) (r%p) := by
  have h := folded base pp (digit B F) light
  rw [pack_digit (by omega) size] at h
  rw [h,digit_pack (by omega) _ (fun j _ => (row_le N p j _).trans_lt (by omega)) (Nat.mod_lt r pp)]

end PolynomePoids687
