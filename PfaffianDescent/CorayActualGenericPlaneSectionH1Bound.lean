import PfaffianDescent.SchemeIsoIntrinsicH1Transport
import PfaffianDescent.CorayProjectiveIntersectionCohomologyOneBound
import PfaffianDescent.CorayActualGenericPlaneSectionSchemeIso
import AllCharacteristics.ProjectiveFiberSmoothness

/-! SOURCE ONLY / UNVERIFIED159. Finite intrinsic H¹ and the bound H¹≤1
for the SAME actual rectangular generic plane cubic. The actual pair
(p_L,H), native n=1 cohomology producer and accepted isomorphism over L
are composed. No elliptic/Riemann--Roch/cohomology-bound hypothesis. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A nonzero linear form is not a multiple of a nonzero cubic. -/
theorem nonzeroLinearForm_not_mem_cubic_span
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0) :
    l ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  intro hmem
  have hdiv : p ∣ l := Ideal.mem_span_singleton.mp hmem
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hl0
  rw [hp.totalDegree hp0, hl.totalDegree hl0] at hle
  omega

/-- Native n=1 intrinsic cohomology, constructing the noncontainment
hypothesis internally from the original homogeneous degrees. -/
theorem smoothCubicLinearPair_unit_cohomology_one_finite_finrank_le_one
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0) :
    let I := projectiveIntersectionIdeal p l hp hl
    let X := scheme I
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      Module.finrank K (schemeModuleCohomology X
        (SheafOfModules.unit X.ringCatSheaf) 1) ≤ 1 := by
  let I := projectiveIntersectionIdeal p l hp hl
  let X := scheme I
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
  have hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
  refine ⟨projectiveIntersection_unit_cohomology_one_finite_native
    p l hp hp0 1 hl hnot, ?_⟩
  simpa only [Nat.sub_self, Nat.mul_zero, Nat.zero_div, Nat.add_zero] using
    projectiveIntersection_unit_cohomology_one_finrank_le_native
      p l hp hp0 1 (by omega) hl hnot

/-- The actual pair is the native projective intersection ideal itself;
only the proofs of homogeneity differ, and these are propositionally
irrelevant. No radical or saturation operation appears. -/
theorem genericPlaneSectionPairIdeal_eq_projectiveIntersection
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    genericPlaneSectionPairIdeal p hp =
      projectiveIntersectionIdeal
        (p.map (algebraMap K (GenericHyperplaneField K)))
        (genericHyperplaneEquation (K := K)) (hp.map _)
        genericHyperplaneEquation_isHomogeneous := rfl

/-- Original-input producer for finite intrinsic H¹ of literal (p_L,H)
and its rank bound. Original K need not be infinite or perfect. -/
theorem smoothCubic_genericPlanePair_unit_cohomology_one_finite_finrank_le_one
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let L := GenericHyperplaneField K
    let I := genericPlaneSectionPairIdeal p hp
    let X := scheme I
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : Linear L X.Modules := schemeModulesLinearOver (toBase I)
    Module.Finite L (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      Module.finrank L (schemeModuleCohomology X
        (SheafOfModules.unit X.ringCatSheaf) 1) ≤ 1 := by
  let L := GenericHyperplaneField K
  let pL := p.map (algebraMap K L)
  let hpL := hp.map (algebraMap K L)
  have hpL0 : pL ≠ 0 := by
    intro hz
    apply hp0
    apply MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective
    simpa only [map_zero] using hz
  letI : Smooth (hypersurfaceToBase pL hpL) :=
    smooth_hypersurfaceToBase_map (algebraMap K L) p hp
  exact smoothCubicLinearPair_unit_cohomology_one_finite_finrank_le_one
    pL (genericHyperplaneEquation (K := K)) hpL hpL0
    genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero

/-- The SAME actual rectangular-substitution plane cubic has finite H¹
of its unit sheaf and original parameter-field rank at most one. This is
an upper bound, not an assertion that its genus equals one. -/
theorem smoothCubic_actualLinearGenericPlaneSection_unit_cohomology_one_finite_finrank_le_one
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let L := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
    let E := hypersurface pE hpE
    letI : EnoughInjectives E.Modules := sheafOfModules_enoughInjectives E.ringCatSheaf
    letI : HasExt.{u} E.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} E.Modules
    letI : Linear L E.Modules := schemeModulesLinearOver (hypersurfaceToBase pE hpE)
    Module.Finite L (schemeModuleCohomology E
      (SheafOfModules.unit E.ringCatSheaf) 1) ∧
      Module.finrank L (schemeModuleCohomology E
        (SheafOfModules.unit E.ringCatSheaf) 1) ≤ 1 := by
  let L := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
  let E := hypersurface pE hpE
  let I := genericPlaneSectionPairIdeal p hp
  let Y := scheme I
  letI : EnoughInjectives E.Modules := sheafOfModules_enoughInjectives E.ringCatSheaf
  letI : HasExt.{u} E.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} E.Modules
  letI : EnoughInjectives Y.Modules := sheafOfModules_enoughInjectives Y.ringCatSheaf
  letI : HasExt.{u} Y.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} Y.Modules
  letI : Linear L E.Modules := schemeModulesLinearOver (hypersurfaceToBase pE hpE)
  letI : Linear L Y.Modules := schemeModulesLinearOver (toBase I)
  have hY := smoothCubic_genericPlanePair_unit_cohomology_one_finite_finrank_le_one
    p hp hp0
  have hE := schemeIso_unit_cohomologyOne_finite_finrank_le
    (hypersurfaceToBase pE hpE) (toBase I) (actualGenericPlanePairSchemeIso p hp)
    (actualGenericPlanePairSchemeIso_hom_toBase p hp) hY.1
  exact ⟨hE.1, hE.2.trans hY.2⟩

end PfaffianDescent.Coray
