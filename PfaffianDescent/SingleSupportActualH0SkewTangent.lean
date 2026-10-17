import PfaffianDescent.SingleSupportIntrinsicSkewTangent
import PfaffianDescent.ActualP3IdealQuadraticGlobalBase

/-! SOURCE ONLY, UNVERIFIED. Literal arithmetic skew-existence lemma with
the genuine H0(I_Z(2)) hypothesis. The dimension dictionary is proved/called
internally on the SAME actual closed immersion. The entire accepted actual
Gamma/dual/chart/nonzero-row/weight conclusion is retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

@[irreducible]
def singleSupport_actual_H0_quadratics_actual_skew_tangents
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition I ((scheme I).fromSpecResidueField P.1))
    (hdim : 3 ≤ finrank k (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap I))) :=
  singleSupport_intrinsic_quadratics_actual_skew_tangents
    I i P hSupport hP hGeom (by
      change 3 ≤ finrank k (SchemeModuleGlobalSectionsOver
        (ambientToBase (R := k) (σ := Fin 4))
        (closedImmersionIdealTwist (i ≫ quotientProjMap I)
          (positiveSheafOfModules (homogeneousSubmodule (Fin 4) k) 2))) at hdim
      rw [p3ActualIdealQuadratic_finrank_eq_intrinsic (i ≫ quotientProjMap I)] at hdim
      exact hdim)

end PfaffianDescent
