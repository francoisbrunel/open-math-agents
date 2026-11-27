import DiviseurTemoin687
import Transfert687
import Semence1223

/-! Transfer a single common residue witness to the formal catalog. -/
namespace CertificatsTransfert687

theorem covered {x H : ℕ} (h : TemoinIntervalle687.Window x H) :
    Green46.IsCoveredByResidues x H := by
  obtain ⟨a,all⟩ := DiviseurTemoin687.prime_cover h
  refine ⟨fun _ => a,fun n hn => ?_⟩
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
  exact all n lo hi

theorem lower {x H : ℕ} (h : TemoinIntervalle687.Window x H) : H ≤ Erdos687.Y x :=
  Transfert687.le_Y_of_covered (covered h)

theorem Y_1223 : 5177 ≤ Erdos687.Y 1223 := lower Semence1223.At200.certificate

end CertificatsTransfert687
