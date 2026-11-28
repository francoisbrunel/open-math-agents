import ProfilsProlongeables687
import Extension687

/-! At linear lengths parity makes each fresh large prime a singleton.
The threshold for an adversarial completion of a random prefix can
therefore be read off from an ordinary survivor count. -/
namespace SeuilDemi687
open Finset Distribution687 ProfilsProlongeables687
open scoped BigOperators

theorem singleton_iff {z x H : ℕ} (hz : 2 ≤ z) (zx : z ≤ x)
    (len : H ≤ 2*(z+1)) (b : Assignment z.primesLE) :
    b ∈ prefixes z x H ↔
      (misses z.primesLE (range H) b).card ≤ (x.primesLE \ z.primesLE).card := by
  classical
  let S := misses z.primesLE (range H) b
  let T := x.primesLE \ z.primesLE
  have two : 2 ∈ z.primesLE := Nat.mem_primesLE.mpr ⟨hz,Nat.prime_two⟩
  constructor
  · intro hb
    obtain ⟨a,agrees,cover⟩ := (mem_filter.mp hb).2
    have fresh (n : ↥S) : ∃ p : ↥T, n.val%p.val=a p.val%p.val := by
      obtain ⟨bound,avoid⟩ := mem_filter.mp n.property
      obtain ⟨p,px,pr,hit⟩ := cover n.val (mem_range.mp bound)
      have out : p ∉ z.primesLE := fun hp => avoid ⟨p,hp⟩ (hit.trans (agrees ⟨p,hp⟩))
      exact ⟨⟨p,mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨px,pr⟩,out⟩⟩,hit⟩
    choose f hf using fresh
    have inj : Function.Injective f := by
      intro i j eq
      let p := (f i).val
      obtain ⟨below,out⟩ := mem_sdiff.mp (f i).property
      have prime : p.Prime := (Nat.mem_primesLE.mp below).2
      have big : z<p := lt_of_not_ge (fun le => out (Nat.mem_primesLE.mpr ⟨le,prime⟩))
      have cop := (Nat.coprime_primes Nat.prime_two prime).mpr (show 2≠p by omega)
      have jp := hf j
      rw [← eq] at jp
      have same : i.val ≡ j.val [MOD p] := (hf i).trans jp.symm
      obtain ⟨iH,ia⟩ := mem_filter.mp i.property
      obtain ⟨jH,ja⟩ := mem_filter.mp j.property
      have ai := ia ⟨2,two⟩
      have aj := ja ⟨2,two⟩
      have ab := (b ⟨2,two⟩).isLt
      change i.val%2 ≠ (b ⟨2,two⟩).val at ai
      change j.val%2 ≠ (b ⟨2,two⟩).val at aj
      change (b ⟨2,two⟩).val<2 at ab
      have parity : i.val ≡ j.val [MOD 2] := by change i.val%2=j.val%2; omega
      have both := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨parity,same⟩
      apply Subtype.ext
      exact both.eq_of_lt_of_lt ((mem_range.mp iH).trans_le (by omega))
        ((mem_range.mp jH).trans_le (by omega))
    simpa [S,T] using Fintype.card_le_of_injective f inj
  · intro budget
    obtain ⟨a,finish⟩ := Extension687.assign_images S T id budget
    let c (p : ℕ) := if hp : p ∈ z.primesLE then (b ⟨p,hp⟩).val else a p
    have old (p : ↥z.primesLE) : c p.val%p.val=(b p).val := by
      simp [c,p.property,Nat.mod_eq_of_lt (b p).isLt]
    refine mem_filter.mpr ⟨mem_univ _,c,old,?_⟩
    intro i hi
    by_cases h : i ∈ S
    · obtain ⟨p,hp,hit⟩ := finish i h
      obtain ⟨inX,out⟩ := mem_sdiff.mp hp
      obtain ⟨px,pr⟩ := Nat.mem_primesLE.mp inX
      exact ⟨p,px,pr,by simp [c,out,hit]⟩
    · have someHit : ∃ p : ↥z.primesLE, i%p.val=(b p).val := by
        by_contra! none
        exact h (mem_filter.mpr ⟨mem_range.mpr hi,none⟩)
      obtain ⟨p,hit⟩ := someHit
      obtain ⟨pz,pr⟩ := Nat.mem_primesLE.mp p.property
      exact ⟨p,pz.trans zx,pr,hit.trans (old p).symm⟩

/-- Count the prefixes on the opposite side of the threshold from the
mean. The bound applies on both sides without an asymptotic hypothesis. -/
theorem opposite_side {z x H : ℕ} (hz : 2 ≤ z) (zx : z ≤ x) (len : H ≤ 2*(z+1)) :
    let μ := (H:ℝ)*∏ p ∈ z.primesLE, (1-(p:ℝ)⁻¹)
    let B := ((x.primesLE \ z.primesLE).card:ℝ)
    let bad := if μ ≤ B then univ \ prefixes z x H else prefixes z x H
    (bad.card:ℝ)*(μ-B)^2 ≤ (H:ℝ)*∏ p ∈ z.primesLE, ((p:ℝ)-1) := by
  classical
  intro μ B bad
  let X (b : Assignment z.primesLE) := ((misses z.primesLE (range H) b).card:ℝ)
  have spread (b) (hb : b ∈ bad) : (μ-B)^2 ≤ (X b-μ)^2 := by
    have ok : b ∈ prefixes z x H ↔ X b ≤ B := by
      simpa only [X,B,Nat.cast_le] using singleton_iff hz zx len b
    by_cases below : μ ≤ B
    · have out : b ∈ univ \ prefixes z x H := by simpa only [bad,if_pos below] using hb
      have high := lt_of_not_ge (fun h => (mem_sdiff.mp out).2 (ok.mpr h))
      nlinarith only [mul_nonneg (sub_nonneg.mpr below) (sub_nonneg.mpr high.le),sq_nonneg (X b-B)]
    · have inside : b ∈ prefixes z x H := by simpa only [bad,if_neg below] using hb
      have low := ok.mp inside
      have up := le_of_lt (lt_of_not_ge below)
      nlinarith only [mul_nonneg (sub_nonneg.mpr up) (sub_nonneg.mpr low),sq_nonneg (B-X b)]
  calc
    _ = ∑ _b ∈ bad, (μ-B)^2 := by simp
    _ ≤ ∑ b ∈ bad, (X b-μ)^2 := sum_le_sum spread
    _ ≤ ∑ b : Assignment z.primesLE, (X b-μ)^2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := Variance687.variance_bound _ (fun _ hp => (Nat.mem_primesLE.mp hp).2) H

end SeuilDemi687
#print axioms SeuilDemi687.singleton_iff
#print axioms SeuilDemi687.opposite_side
