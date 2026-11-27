import Extension687

/-! A positive integer weight certificate can rule out all completions of
    a residual sieve, even when the unweighted sum of capacities is too big. -/
namespace Ponderation687

def mass (S : Finset ℕ) (w : ℕ → ℕ) (p r : ℕ) : ℕ :=
  ∑ n ∈ S, if n%p = r%p then w n else 0

theorem necessary {S P : Finset ℕ} (w : ℕ → ℕ) (a : ℕ → ℕ)
    (cover : ∀ n ∈ S, ∃ p ∈ P, n%p = a p%p) :
    ∑ n ∈ S, w n ≤ ∑ p ∈ P, mass S w p (a p) := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨p,hp,eq⟩ := cover n hn
  have one := Finset.single_le_sum (f := fun q : ℕ => if n%q = a q%q then w n else 0)
    (fun _ _ => Nat.zero_le _) hp
  simpa only [if_pos eq] using one

theorem excludes {S P : Finset ℕ} (w c : ℕ → ℕ)
    (capacity : ∀ p ∈ P, ∀ r, mass S w p r ≤ c p)
    (gap : ∑ p ∈ P, c p < ∑ n ∈ S, w n) :
    ¬Extension687.Completes S P := by
  rintro ⟨a,all⟩
  exact (Nat.not_lt_of_ge ((necessary w a all).trans
    (Finset.sum_le_sum (fun p hp => capacity p hp (a p)))) ) gap

theorem upper {x z H : ℕ}
    (cert : ∀ a : ℕ → ℕ, let S := Transfert687.survivors z H a
       let P := x.primesLE \ z.primesLE
       ∃ w c : ℕ → ℕ, (∀ p ∈ P, ∀ r, mass S w p r ≤ c p) ∧
         ∑ p ∈ P, c p < ∑ n ∈ S, w n) : Erdos687.Y x < H := by
  by_contra! le
  obtain ⟨a,all⟩ := Extension687.optimal_cover x
  obtain ⟨w,c,cap,strict⟩ := cert a
  apply excludes w c cap strict
  refine ⟨a,fun n hn => ?_⟩
  obtain ⟨since,avoid⟩ := Finset.mem_filter.mp hn
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp since
  obtain ⟨p,px,pr,hit⟩ := all n (Finset.mem_Icc.mpr ⟨lo,hi.trans le⟩)
  exact ⟨p,Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨px,pr⟩,fun q => avoid p q hit⟩,hit⟩

end Ponderation687
