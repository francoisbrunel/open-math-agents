import DensiteCarree687

/-! Exact elimination of the last two prime rows by forbidden sets of
at most four survivor positions. The support bound is sharp. -/
namespace QuatreTemoins687
open scoped BigOperators

def Two (S : Finset ℕ) (f g : ℕ → ℕ) : Prop :=
  ∃ u v : ℕ, ∀ n ∈ S, f n=u ∨ g n=v

private theorem swap (S : Finset ℕ) (f g : ℕ → ℕ) : Two S f g ↔ Two S g f := by
  constructor <;> rintro ⟨u,v,h⟩ <;> exact ⟨v,u,fun n hn => (h n hn).symm⟩

private theorem two_values (S : Finset ℕ) (g : ℕ → ℕ)
    (no : ¬ ∃ v : ℕ, ∀ n ∈ S, g n=v) :
    ∃ i ∈ S, ∃ j ∈ S, g i ≠ g j := by
  by_contra! same
  rcases S.eq_empty_or_nonempty with empty | ⟨i,hi⟩
  · exact no ⟨0,by simp [empty]⟩
  · exact no ⟨g i,fun n hn => same n hn i hi⟩

private theorem one_forced {S : Finset ℕ} {f g : ℕ → ℕ} (bad : ¬ Two S f g)
    {i j : ℕ} (hi : i∈S) (hj : j∈S) (row : f i=f j) (diff : g i≠g j) :
    ∃ W ⊆ S, W.card ≤ 4 ∧ ¬ Two W f g := by
  classical
  let R := S.filter (fun n => f n≠f i)
  have no : ¬ ∃ v : ℕ, ∀ n ∈ R, g n=v := by
    rintro ⟨v,hv⟩
    apply bad
    refine ⟨f i,v,?_⟩
    intro n hn
    by_cases h : f n=f i
    · exact Or.inl h
    · exact Or.inr (hv n (Finset.mem_filter.mpr ⟨hn,h⟩))
  obtain ⟨a,ha,b,hb,ab⟩ := two_values R g no
  obtain ⟨as,af⟩ := Finset.mem_filter.mp ha
  obtain ⟨bs,bf⟩ := Finset.mem_filter.mp hb
  let W : Finset ℕ := {i,j,a,b}
  have sub : W ⊆ S := by
    intro n hn
    simp only [W,Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl|rfl <;> assumption
  have size : W.card ≤ 4 := by
    dsimp [W]
    calc _ ≤ (({j,a,b}:Finset ℕ).card)+1 := Finset.card_insert_le _ _
         _ ≤ (({a,b}:Finset ℕ).card+1)+1 := by gcongr; apply Finset.card_insert_le
         _ ≤ ((({b}:Finset ℕ).card+1)+1)+1 := by gcongr; apply Finset.card_insert_le
         _ = _ := by simp
  refine ⟨W,sub,size,?_⟩
  rintro ⟨u,v,h⟩
  have I := h i (by simp [W])
  have J := h j (by simp [W])
  have A := h a (by simp [W])
  have B := h b (by simp [W])
  grind

/-- If every at-most-four-point subset is coverable by a row of each
kind, then one pair of rows works on the entire set. -/
theorem small_obstruction {S : Finset ℕ} {f g : ℕ → ℕ} (bad : ¬ Two S f g) :
    ∃ W ⊆ S, W.card ≤ 4 ∧ ¬ Two W f g := by
  classical
  by_cases splitF : ∃ i ∈ S, ∃ j ∈ S, f i=f j ∧ g i≠g j
  · obtain ⟨i,hi,j,hj,eq,ne⟩ := splitF
    exact one_forced bad hi hj eq ne
  by_cases splitG : ∃ i ∈ S, ∃ j ∈ S, g i=g j ∧ f i≠f j
  · obtain ⟨i,hi,j,hj,eq,ne⟩ := splitG
    obtain ⟨W,sub,size,no⟩ := one_forced (fun h => bad ((swap S f g).mpr h)) hi hj eq ne
    exact ⟨W,sub,size,fun h => no ((swap W f g).mp h)⟩
  push Not at splitF splitG
  have no : ¬ ∃ v : ℕ, ∀ n ∈ S, g n=v := by
    rintro ⟨v,h⟩
    exact bad ⟨0,v,fun n hn => Or.inr (h n hn)⟩
  obtain ⟨i,hi,j,hj,ng⟩ := two_values S g no
  have nf : f i≠f j := fun eq => ng (splitF i hi j hj eq)
  have outside : ¬ ∀ n ∈ S, f n=f i ∨ g n=g j := fun h => bad ⟨_,_,h⟩
  push Not at outside
  obtain ⟨k,hk,kf,kg⟩ := outside
  have kgi : g k≠g i := fun h => kf (splitG k hk i hi h)
  have kfj : f k≠f j := fun h => kg (splitF k hk j hj h)
  let W : Finset ℕ := {i,j,k}
  have sub : W ⊆ S := by
    intro n hn
    simp only [W,Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl <;> assumption
  have size : W.card ≤ 4 := by
    have h1 := Finset.card_insert_le i ({j,k}:Finset ℕ)
    have h2 := Finset.card_insert_le j ({k}:Finset ℕ)
    simp only [Finset.card_singleton] at h2
    dsimp [W]; omega
  refine ⟨W,sub,size,?_⟩
  rintro ⟨u,v,h⟩
  have I := h i (by simp [W])
  have J := h j (by simp [W])
  have K := h k (by simp [W])
  grind

/-- A family of other rows can be extended by p and q precisely when
it has already hit every forbidden subset of size at most four. -/
theorem extend_iff_hits (S : Finset ℕ) (p q : ℕ) (hit : ℕ → Prop) :
    (∃ u v : ℕ, ∀ n ∈ S, hit n ∨ n%p=u ∨ n%q=v) ↔
      ∀ W ⊆ S, W.card ≤ 4 → ¬ Two W (·%p) (·%q) → ∃ n ∈ W, hit n := by
  classical
  constructor
  · rintro ⟨u,v,h⟩ W sub _ no
    by_contra! missing
    exact no ⟨u,v,fun n hn => (h n (sub hn)).resolve_left (missing n hn)⟩
  · intro all
    let T := S.filter (fun n => ¬ hit n)
    have yes : Two T (·%p) (·%q) := by
      by_contra no
      obtain ⟨W,sub,size,bad⟩ := small_obstruction no
      obtain ⟨n,hn,covered⟩ := all W (sub.trans (Finset.filter_subset _ S)) size bad
      exact (Finset.mem_filter.mp (sub hn)).2 covered
    obtain ⟨u,v,h⟩ := yes
    refine ⟨u,v,?_⟩
    intro n hn
    by_cases ok : hit n
    · exact Or.inl ok
    · exact Or.inr (h n (Finset.mem_filter.mpr ⟨hn,ok⟩))

def load (F : Finset (Finset ℕ)) (r t : ℕ) : ℕ :=
  (F.filter (fun W => ∃ n ∈ W, n%r=t%r)).card

/-- The load of each outside prime is measured on forbidden sets, not
on their individual positions. This permits overlapping witnesses. -/
theorem family_budget {S R : Finset ℕ} {p q : ℕ} (F : Finset (Finset ℕ))
    (members : ∀ W ∈ F, W ⊆ S ∧ ¬ Two W (·%p) (·%q))
    (a : ℕ → ℕ) (cover : ∀ n ∈ S,
      (∃ r ∈ R, n%r=a r%r) ∨ n%p=a p%p ∨ n%q=a q%q) :
    F.card ≤ ∑ r ∈ R, load F r (a r) := by
  classical
  let C (r : ℕ) := F.filter (fun W => ∃ n ∈ W, n%r=a r%r)
  have sub : F ⊆ R.biUnion C := by
    intro W hw
    obtain ⟨ws,no⟩ := members W hw
    by_contra missing
    apply no
    refine ⟨a p%p,a q%q,?_⟩
    intro n hn
    refine (cover n (ws hn)).resolve_left ?_
    rintro ⟨r,hr,eq⟩
    exact missing (Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_filter.mpr ⟨hw,n,hn,eq⟩⟩)
  exact (Finset.card_le_card sub).trans Finset.card_biUnion_le

/-- Four odd positions form a minimal obstruction for the last two
primes 3 and 5. Each deletion is covered by the opposite row and column. -/
theorem sharp :
    let W : Finset ℕ := {1,7,11,17}
    ¬ Two W (·%3) (·%5) ∧ ∀ n ∈ W, Two (W.erase n) (·%3) (·%5) := by
  dsimp only
  constructor
  · rintro ⟨u,v,h⟩
    have a := h 1 (by decide)
    have b := h 7 (by decide)
    have c := h 11 (by decide)
    have d := h 17 (by decide)
    norm_num at a b c d
    omega
  · intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl|rfl
    · exact ⟨2,2,by decide⟩
    · exact ⟨2,1,by decide⟩
    · exact ⟨1,2,by decide⟩
    · exact ⟨1,1,by decide⟩

end QuatreTemoins687
#print axioms QuatreTemoins687.small_obstruction
#print axioms QuatreTemoins687.extend_iff_hits
#print axioms QuatreTemoins687.family_budget
#print axioms QuatreTemoins687.sharp
