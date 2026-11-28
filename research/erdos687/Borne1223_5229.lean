import Couverture1223_5229
import DiviseurTemoin687
import Transfert687

namespace Couverture1223_5229

/-- The complete 5,229-position cover in the catalogue's conventions. -/
theorem lower_bound : 5229 ≤ Erdos687.Y 1223 := by
  apply Transfert687.le_Y_of_covered
  obtain ⟨a, ha⟩ := DiviseurTemoin687.prime_cover At200.certificate
  refine ⟨fun _ => a, fun n hn => ?_⟩
  obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp hn
  exact ha n lo hi

end Couverture1223_5229

#print axioms Couverture1223_5229.lower_bound
