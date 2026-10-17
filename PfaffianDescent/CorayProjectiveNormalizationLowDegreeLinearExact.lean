import PfaffianDescent.CorayGenericNormalizationLowDegreeLinearExact
import PfaffianDescent.CorayProjectiveNormalizationLowDegreeExact

/-! Literal original p/q caller for the actual K-linear normalization LES
ending in intrinsic H¹ of the actual normalization. Original Q and all
maps are retained; no finite-dimensionality or constants/genus input.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual linear sequence from the literal smooth cubic/projective p/q
intersection: exact at Hom(O_X,Q) and H¹_X(O_X), surjective onto intrinsic
H¹_N(O_N), and the actual K-linear kernel equals the actual connecting range.
Support, affine choice, local Q/QC/Ext, HasExt and comparison are internal. -/
theorem projectiveIntersection_genericNormalization_lowDegreeLinearExact_surjective_and_kernel
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase I)
    Function.Exact (genericNormalizationHomQuotientLinearMap X (toBase I))
      (genericNormalizationHomConnectingLinearMap X (toBase I)) ∧
    Function.Exact (genericNormalizationHomConnectingLinearMap X (toBase I))
      (genericNormalizationCohomologyOneToNormalizationLinearMap X (toBase I)) ∧
    Function.Surjective (genericNormalizationCohomologyOneToNormalizationLinearMap X (toBase I)) ∧
    (genericNormalizationCohomologyOneToNormalizationLinearMap X (toBase I)).ker =
      LinearMap.range (genericNormalizationHomConnectingLinearMap X (toBase I)) := by
  intro I X N ν
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase I)
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  obtain ⟨U, _, hsU, _⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_affineOpen
      p q hp hp0 n hq hnot (genericPoint X)
  have hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)) :=
    projectiveIntersection_genericNormalizationQuotient_stalkSupport_isClosed
      p q hp hp0 n hq hnot
  have hlinear := genericNormalization_lowDegreeLinearMaps_exact X (toBase I)
  have hintrinsic := genericNormalization_connecting_intrinsicCohomologyOne_exact_and_kernel X (toBase I)
  have hsurj : Function.Surjective
      (genericNormalizationCohomologyOneToNormalizationLinearMap X (toBase I)) :=
    genericNormalization_intrinsicCohomologyOneLinearMap_surjective_of_closedSupport_subset_affine
      X (toBase I) hclosed U.1 U.2 hsU
  exact ⟨hlinear.1, hintrinsic.1, hsurj, hintrinsic.2⟩

end PfaffianDescent.Coray
