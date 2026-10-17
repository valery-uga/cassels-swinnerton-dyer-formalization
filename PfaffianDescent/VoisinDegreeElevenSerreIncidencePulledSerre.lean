import PfaffianDescent.VoisinDegreeElevenSerreIncidencePulledLocallyFree
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFlatPulledSequence

/-! # Actual Serre pullback along a flat surface morphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidencePulledSerre
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f] {N : X.Modules}
    (e : SerreExtensionData X N) (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    SerreExtensionData Y ((Scheme.Modules.pullback f).obj N) :=
  SerreExtensionData.ofSequence (serreIncidenceFlatPulledSequence f e)
    (serreIncidencePulled_locallyFree f e C)

end PfaffianDescent
