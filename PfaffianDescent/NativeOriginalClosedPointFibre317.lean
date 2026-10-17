import PfaffianDescent.NativeClosedChartBaseChange312
import Mathlib.Topology.JacobsonSpace

/-! SOURCE ONLY317. Exact whole ideal reduction to an original closed point
constructs the single-point fibre square required by the original195 lift. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (d : Y ⟶ X)
  (P : closedPoints Y)
  (h : I.comap d = (Y.fromSpecResidueField P.val).ker)

/-- The point-to-whole-family map is constructed from the actual ideal. -/
def nativeOriginalClosedPointFibreMap317 : Spec (Y.residueField P.val) ⟶ I.subscheme := by
  letI : IsClosedImmersion (Y.fromSpecResidueField P.val) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.property
  exact nativeClosedChartToGlobal312 I d (Y.fromSpecResidueField P.val) h

lemma nativeOriginalClosedPointFibreMap_isPullback317 :
    IsPullback (nativeOriginalClosedPointFibreMap317 I d P h)
      (Y.fromSpecResidueField P.val) I.subschemeι d := by
  letI : IsClosedImmersion (Y.fromSpecResidueField P.val) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.property
  exact (nativeClosedChartToGlobal_isPullback312 I d
    (Y.fromSpecResidueField P.val) h).flip

lemma nativeOriginalClosedPointFibreMap_comp317 :
    nativeOriginalClosedPointFibreMap317 I d P h ≫ I.subschemeι =
      Y.fromSpecResidueField P.val ≫ d := by
  letI : IsClosedImmersion (Y.fromSpecResidueField P.val) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.property
  exact nativeClosedChartToGlobal_comp312 I d (Y.fromSpecResidueField P.val) h

end PfaffianDescent
end
