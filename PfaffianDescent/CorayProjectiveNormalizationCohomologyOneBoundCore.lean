import PfaffianDescent.CorayProjectiveIntersectionCohomologyOneBound
import PfaffianDescent.CorayProjectiveNormalizationIntrinsicH1FiniteCore

/-! Independently staged coarse original-K normalization H¹ bound.
The original theorem declaration below is copied byte-for-byte.
Actual curve bound and normalization surjection remain internally derived.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Primitive rank bound for H¹ of the ACTUAL original normalization unit.
All finite-dimensionality, native Ext and surjectivity are internal; the
normalization action is independently induced by ν composed with toBase I. -/
theorem projectiveIntersection_genericNormalization_unit_cohomology_one_finrank_le_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase I)
    Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) ≤
      1 + 3 * n * (n - 1) / 2 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : LocallyOfFiniteType pi := inferInstance
  letI : Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) :=
    projectiveIntersection_unit_cohomology_one_finite_native p q hp hp0 n hq hnot
  letI : Module.Finite K (schemeModuleCohomology N
      (SheafOfModules.unit N.ringCatSheaf) 1) :=
    projectiveIntersection_genericNormalization_unit_cohomology_one_finite_native p q hp hp0 n hq hnot
  let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
  have hsurj : Function.Surjective g :=
    (projectiveIntersection_genericNormalization_lowDegreeLinearExact_surjective_and_kernel
      p q hp hp0 n hq hnot).2.2.1
  exact (LinearMap.finrank_le_finrank_of_surjective hsurj).trans
    (projectiveIntersection_unit_cohomology_one_finrank_le_native p q hp hp0 n hn hq hnot)

end PfaffianDescent.Coray
