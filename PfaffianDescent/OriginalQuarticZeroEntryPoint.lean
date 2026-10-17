import PfaffianDescent.IndependentPerfectDegreeFourPointSection
import PfaffianDescent.PerfectFieldQuarticPointChartBasis

/-! The POINT conclusion of Proposition prop:zero-off-diagonal for the SAME
original cubic, closed point and supplied Z follows from the independent
perfect-field degree-four theorem. No claim
about graph shape, tangent-line descent, finite full base, or equality of base
schemes is made by this export.  Those are separate mathematical assertions. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The point conclusion follows from a smaller subset of its hypotheses
using the independent perfect-field tangent-net theorem. The original Z and
its rank/support are retained. This does not certify the supplied-Z graph,
matching-line or four-cycle constructions in the written proof. -/
theorem sectionFour_originalZ_zero_entry_point_conclusion
    {k : Type u} [Field k] [PerfectField k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (P : closedPoints (hypersurface F hF))
    (hP : (hypersurfaceToBase F hF).residueDegree P.1 = 4)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase F hF)]
    (_hSupport : Set.range i = {P.1})
    (_hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase F hF) = 8)
    (_hGeom : ProjectiveGeometricGeneralPosition (equationIdeal F hF)
      ((hypersurface F hF).fromSpecResidueField P.1)) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ :=
  independent_perfectField_degree_four_closed_point_rational_section F hF hF0 P hP

end PfaffianDescent
