import PfaffianDescent.ActualP3QuadraticRestrictionChartComparison

/-! UNVERIFIED: the full base ideal formed from genuine ideal-sheaf global
sections, using their internally derived canonical polynomial coordinates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ActualP3IdealQuadraticHZero
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i] :=
  SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
    (closedImmersionIdealTwist i
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))

def p3ActualIdealQuadraticPolynomialLinearMap
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i] :
    ActualP3IdealQuadraticHZero i →ₗ[K] MvPolynomial (Fin 4) K :=
  (intrinsicFullQuadraticSystem i).subtype.comp
    (p3ActualIdealQuadraticIntrinsicLinearEquiv i).toLinearMap

theorem p3ActualIdealQuadraticPolynomialLinearMap_range
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i] :
    (p3ActualIdealQuadraticPolynomialLinearMap i).range =
      intrinsicFullQuadraticSystem i := by
  ext p
  constructor
  · rintro ⟨s, rfl⟩
    exact (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).property
  · intro hp
    let q : intrinsicFullQuadraticSystem i := ⟨p, hp⟩
    refine ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv i).symm q, ?_⟩
    exact congrArg Subtype.val
      ((p3ActualIdealQuadraticIntrinsicLinearEquiv i).apply_symm_apply q)

theorem p3ActualIdealQuadraticPolynomialLinearMap_range_homogeneous
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i]
    (p : MvPolynomial (Fin 4) K)
    (hp : p ∈ (p3ActualIdealQuadraticPolynomialLinearMap i).range) :
    p.IsHomogeneous 2 := by
  rw [p3ActualIdealQuadraticPolynomialLinearMap_range] at hp
  exact intrinsicFullQuadraticSystem_homogeneous i p hp

def p3ActualIdealQuadraticGlobalBaseIdeal
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i] :=
  quadraticSystemBaseLocusIdeal (p3ActualIdealQuadraticPolynomialLinearMap i).range
    (p3ActualIdealQuadraticPolynomialLinearMap_range_homogeneous i)

theorem p3ActualIdealQuadraticGlobalBaseIdeal_eq_intrinsic
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i] :
    p3ActualIdealQuadraticGlobalBaseIdeal i = intrinsicFullQuadraticBaseIdeal i := by
  apply HomogeneousIdeal.toIdeal_injective
  change Ideal.span ((p3ActualIdealQuadraticPolynomialLinearMap i).range :
      Set (MvPolynomial (Fin 4) K)) =
    Ideal.span (intrinsicFullQuadraticSystem i : Set (MvPolynomial (Fin 4) K))
  rw [p3ActualIdealQuadraticPolynomialLinearMap_range]

end PfaffianDescent
