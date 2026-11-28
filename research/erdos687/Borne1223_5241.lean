import Couverture1223_5241
import DiviseurTemoin687
import Transfert687

namespace Couverture1223_5241

/-- The complete 5,241-position cover in the catalogue's conventions. -/
theorem lower_bound : 5241 ≤ Erdos687.Y 1223 := by
  apply Transfert687.le_Y_of_covered
  obtain ⟨a, ha⟩ := DiviseurTemoin687.prime_cover At200.certificate
  refine ⟨fun _ => a, fun n hn => ?_⟩
  obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp hn
  exact ha n lo hi

end Couverture1223_5241

#print axioms Couverture1223_5241.lower_bound
