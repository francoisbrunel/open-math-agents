import Extension687

/-! Transport the primorial covering theorem of the tilted-cover
    formalization to the exact catalog conventions. -/
namespace BorneInclinee687
open Filter
open scoped Asymptotics

/-- Right side of Erdos4.Tilted.boundedCover_iff_residues. -/
def Covered (z h : ℕ) : Prop := ∃ a : ℕ → ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ h →
  ∃ p : ℕ, p.Prime ∧ p ≤ z ∧ i ≡ a p [MOD p]

theorem covered_iff {z h : ℕ} : Covered z h ↔ Green46.IsCoveredByResidues z h := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,fun i hi => ?_⟩
    obtain ⟨lo,up⟩ := Finset.mem_Icc.mp hi
    obtain ⟨p,pr,le,hit⟩ := ha i lo up
    exact ⟨p,le,pr,hit⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,fun i lo up => ?_⟩
    obtain ⟨p,le,pr,hit⟩ := ha i (Finset.mem_Icc.mpr ⟨lo,up⟩)
    exact ⟨p,pr,le,hit⟩

theorem same_maximum (M : ℝ → ℕ) (found : ∀ X : ℝ, Covered ⌊X⌋₊ (M X))
    (upper : ∀ (X : ℝ) (y : ℕ), Covered ⌊X⌋₊ y → y ≤ M X) (x : ℕ) :
    M x = Erdos687.Y x := by
  apply le_antisymm
  · exact Transfert687.le_Y_of_covered (covered_iff.mp (by simpa using found (x:ℝ)))
  · apply upper
    simpa using covered_iff.mpr (Extension687.optimal_cover x)

/-- A single bound on the source maximum gives a one-sided bound for
    the catalog's Y with exactly the same scale and existential constant. -/
theorem lower (M : ℝ → ℕ) (found : ∀ X : ℝ, Covered ⌊X⌋₊ (M X))
    (upper : ∀ (X : ℝ) (y : ℕ), Covered ⌊X⌋₊ y → y ≤ M X)
    (source : ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c*X*Real.log X/Real.log (Real.log (Real.log X)) ≤ (M X:ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      c*x*Real.log x/Real.log (Real.log (Real.log x)) ≤ (Erdos687.Y x:ℝ) := by
  obtain ⟨c,X₀,hc,hs⟩ := source
  refine ⟨c,hc,?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop).eventually_ge_atTop X₀]
    with x hx
  simpa only [same_maximum M found upper x] using hs x hx

end BorneInclinee687
