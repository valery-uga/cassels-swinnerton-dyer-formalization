import PfaffianDescent.ActualPositiveTwoTrivializedQuotientScalar
import PfaffianDescent.ActualOriginalQuarticGlobalLineEmbedding
import PfaffianDescent.ActualClosedEmbeddedSchemeIdealIso

/- SOURCE ONLY / UNVERIFIED. Arbitrary ACTUAL O(2) point Isos retain the
SAME original embedded ideal; the ambient source Iso is derived from it. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)

/-- Construction from an arbitrary actual twist trivialization. -/
def actualOriginalPositiveTwoTrivializedEmbedding
    (e : (Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of ((hypersurface p hp).residueField P.1))).ringCatSheaf)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp
      ((hypersurface p hp).fromSpecResidueField P.1) →ₗ[(hypersurface p hp).residueField P.1]
        (hypersurface p hp).residueField P.1) :=
  actualOriginalQuarticGlobalLineEmbedding p hp P hP
    (actualPositiveTwoTrivializedQuotient p hp _ e ell)

theorem actualOriginalPositiveTwoTrivializedEmbedding_ideal_eq
    (e0 e1 : (Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of ((hypersurface p hp).residueField P.1))).ringCatSheaf)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp
      ((hypersurface p hp).fromSpecResidueField P.1) →ₗ[(hypersurface p hp).residueField P.1]
        (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    (actualOriginalPositiveTwoTrivializedEmbedding p hp P hP e0 ell).ker =
      (actualOriginalPositiveTwoTrivializedEmbedding p hp P hP e1 ell).ker := by
  apply (actualOriginalQuarticGlobalLineEmbedding_ideal_eq_iff_nonzero_scale p hp P hP
    _ _ (actualPositiveTwoTrivializedQuotient_surjective p hp _ e0 ell hell)
      (actualPositiveTwoTrivializedQuotient_surjective p hp _ e1 ell hell)).2
  exact ⟨(actualPointTwistTrivializationScalar e0 e1)⁻¹,
    inv_ne_zero (actualPointTwistTrivializationScalar_ne_zero e0 e1),
      actualPositiveTwoTrivializedQuotient_inverse_scalar p hp _ e0 e1 ell⟩

theorem actualOriginalPositiveTwoTrivializedEmbedding_exists_over_iso
    (e0 e1 : (Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of ((hypersurface p hp).residueField P.1))).ringCatSheaf)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp
      ((hypersurface p hp).fromSpecResidueField P.1) →ₗ[(hypersurface p hp).residueField P.1]
        (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    ∃ E : Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))) ≅
        Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))),
      E.hom ≫ actualOriginalPositiveTwoTrivializedEmbedding p hp P hP e1 ell =
        actualOriginalPositiveTwoTrivializedEmbedding p hp P hP e0 ell := by
  let a := actualOriginalPositiveTwoTrivializedEmbedding p hp P hP e0 ell
  let b := actualOriginalPositiveTwoTrivializedEmbedding p hp P hP e1 ell
  letI : IsClosedImmersion a :=
    (actualOriginalQuarticGlobalLineEmbedding_actual_tangent p hp P hP _
      (actualPositiveTwoTrivializedQuotient_surjective p hp _ e0 ell hell)).1
  letI : IsClosedImmersion b :=
    (actualOriginalQuarticGlobalLineEmbedding_actual_tangent p hp P hP _
      (actualPositiveTwoTrivializedQuotient_surjective p hp _ e1 ell hell)).1
  exact (actualClosedEmbeddedScheme_ideal_eq_iff_ambient_iso a b).1
    (actualOriginalPositiveTwoTrivializedEmbedding_ideal_eq p hp P hP e0 e1 ell hell)

end PfaffianDescent
