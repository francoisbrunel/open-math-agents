import ClassesImposees687
import DensiteCarree687

/-! A long covering interval forces a whole arithmetic progression of
simultaneously thin profiles in each prescribed small-prime cylinder. -/
namespace TranslationsCarrees687
open Filter Transfert687

def slide (d : ℕ) (a : ℕ → ℕ) (p : ℕ) := a p+(p-1)*d

private theorem back (d : ℕ) (a : ℕ → ℕ) {p : ℕ} (hp : 0 < p) :
    slide d a p+d ≡ a p [MOD p] := by
  have eq : slide d a p+d = a p+p*d := by
    unfold slide
    have add : p-1+1=p := by omega
    calc
      _ = a p+(p-1+1)*d := by ring
      _ = _ := by rw [add]
  rw [eq]
  simpa using (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right p d)).add_left (a p)

theorem preserved {d w : ℕ} (step : primorial w ∣ d) (a : ℕ → ℕ)
    {p : ℕ} (hp : p ∈ w.primesLE) : slide d a p ≡ a p [MOD p] := by
  obtain ⟨small,pr⟩ := Nat.mem_primesLE.mp hp
  have dv := (pr.dvd_primorial_iff.mpr small).trans step
  simpa [slide] using (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right dv (p-1))).add_left (a p)

/-- Each member uses the same base assignment, including all the larger
rows. The initial alignment to an arbitrary small prefix costs D-1. -/
theorem progression {x H T w : ℕ} (b : ℕ → ℕ)
    (long : H+T*primorial w+(primorial w-1) ≤ Erdos687.Y x) :
    ∃ a : ℕ → ℕ, (∀ p ∈ w.primesLE, a p ≡ b p [MOD p]) ∧
      ∀ j ≤ T, ∀ n ∈ Finset.Icc 1 H,
        ∃ p ≤ x, p.Prime ∧ n ≡ slide (j*primorial w) a p [MOD p] := by
  obtain ⟨a,agree,full⟩ := ClassesImposees687.at_maximum x w.primesLE
    (fun p hp => (Nat.mem_primesLE.mp hp).2) b
  rw [← primorial_eq_prod_primesLE] at full
  refine ⟨a,agree,?_⟩
  intro j jT n hn
  obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hn
  have shift := Nat.mul_le_mul_right (primorial w) jT
  obtain ⟨p,px,pr,hit⟩ := full (n+j*primorial w) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  exact ⟨p,px,pr,Nat.ModEq.add_right_cancel' _ (hit.trans (back _ a pr.pos).symm)⟩

/-- At the square scale it suffices to find one thick translate in
each short progression starting in one chosen cylinder. -/
theorem obstruction (m : ℕ) (hm : 2 ≤ m) :
    ∀ᶠ k : ℕ in atTop, let z := k^m
      ∀ (w T : ℕ) (b : ℕ → ℕ),
      (∀ a : ℕ → ℕ, (∀ p ∈ w.primesLE, a p ≡ b p [MOD p]) →
        ∃ j ≤ T, (24/(m:ℝ))*(z:ℝ)^2/Real.log z <
          ((survivors z (z^2) (slide (j*primorial w) a)).card:ℝ)) →
      Erdos687.Y (k^(m+1)) < z^2+T*primorial w+(primorial w-1) := by
  filter_upwards [DensiteCarree687.thin_of_cover m hm] with k thin
  dsimp only
  intro w T b thick
  by_contra! long
  obtain ⟨a,agree,all⟩ := progression b long
  obtain ⟨j,jT,large⟩ := thick a agree
  exact (not_lt_of_ge (thin _ (all j jT))) large

end TranslationsCarrees687
#print axioms TranslationsCarrees687.progression
#print axioms TranslationsCarrees687.obstruction
