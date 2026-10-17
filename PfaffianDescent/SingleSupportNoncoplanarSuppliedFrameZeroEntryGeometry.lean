import PfaffianDescent.SingleSupportOriginalSuppliedFrameZeroEntryGeometry
import PfaffianDescent.PerfectFieldClosedPointGeometricPosition

/-! SOURCE ONLY, UNVERIFIED. Thin original noncoplanarity frontend. Actual
geometric general position is DERIVED internally by the accepted perfect-
field closed-point provider, not passed as an unexplained certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
@[irreducible]
def singleSupport_noncoplanarOriginalZ_supplied_frame_epsilon_zero_entry_geometry
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] (P : closedPoints (hypersurface p hp))
    (hSupport : Set.range i = {P.1})
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (hplane : ¬ ∃ c : Fin 4 → k, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal) :=
  letI : IsFinite (i ≫ toBase (equationIdeal p hp)) := by
    change IsFinite (i ≫ hypersurfaceToBase p hp)
    infer_instance
  singleSupport_originalZ_supplied_frame_epsilon_zero_entry_geometry
    p hp i P hSupport hP
    (perfectField_cubic_closedPoint_degree_four_general_position p hp P hP hplane)

end PfaffianDescent
