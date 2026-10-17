import PfaffianDescent.ActualOriginalPositiveTwoTrivializationEmbeddedIdeal

/- SOURCE ONLY / UNVERIFIED. The canonical existing untwist is one ACTUAL
trivialization. Arbitrary alternatives construct the SAME ambient ideal. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

@[simp] theorem actualPositiveTwoTrivializedFiberEquiv_canonical
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp) :
    actualPositiveTwoTrivializedFiberEquiv p hp q
      (actualFieldPointPositiveTwistUnitIso (equationIdeal p hp) q 2) =
        actualCubicPositiveTwoDifferentialPointFiberEquiv p hp q := rfl

@[simp] theorem actualPositiveTwoTrivializedQuotient_canonical
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp q →ₗ[L] L) :
    actualPositiveTwoTrivializedQuotient p hp q
      (actualFieldPointPositiveTwistUnitIso (equationIdeal p hp) q 2) ell =
        actualPositiveTwo_globalLineEquiv p hp q ell := rfl

theorem actualOriginalPositiveTwoTrivialization_ideal_eq_canonical
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (e : (Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of ((hypersurface p hp).residueField P.1))).ringCatSheaf)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp
      ((hypersurface p hp).fromSpecResidueField P.1) →ₗ[(hypersurface p hp).residueField P.1]
        (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    (actualOriginalPositiveTwoTrivializedEmbedding p hp P hP e ell).ker =
      (actualOriginalQuarticGlobalLineEmbedding p hp P hP
        (actualPositiveTwo_globalLineEquiv p hp
          ((hypersurface p hp).fromSpecResidueField P.1) ell)).ker := by
  exact actualOriginalPositiveTwoTrivializedEmbedding_ideal_eq p hp P hP e
    (actualFieldPointPositiveTwistUnitIso (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField P.1) 2) ell hell

end PfaffianDescent
