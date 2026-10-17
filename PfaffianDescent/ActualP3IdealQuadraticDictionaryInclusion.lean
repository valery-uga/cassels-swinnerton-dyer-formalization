import PfaffianDescent.ActualP3QuadraticRestrictionChartComparison

/- SOURCE ONLY / UNVERIFIED. The exact actual H0 dictionary retains the
original AMBIENT ideal inclusion as the actual homogeneous global section.
No polynomial/global-section inclusion comparison is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma p3ActualIdealQuadraticIntrinsicLinearEquiv_inclusion
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i]
    (s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2))) :
    s ≫ (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)).f ≫
      (schemeModuleTensorUnitLeftIso
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)).hom =
    p3HomogeneousGlobalSectionLinearMap K 2
      ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv i s).val,
        (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).property.1⟩ := by
  let e := p3HomogeneousGlobalSectionsLinearEquiv K 2 (by decide)
  let T := positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2
  let inc := (closedImmersionIdealTwistSequence i T).f ≫
    (schemeModuleTensorUnitLeftIso T).hom
  change s ≫ inc = e (e.symm (s ≫ inc))
  exact (e.apply_symm_apply (s ≫ inc)).symm

end PfaffianDescent
