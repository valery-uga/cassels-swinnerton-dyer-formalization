import PfaffianDescent.CorayCubicLinearPairH1RankOne

/-! SOURCE ONLY / UNVERIFIED161. Original smooth cubic inputs construct
EXACT native unit H1 rank1 for the SAME entire pair and SAME actual
rectangular generic plane cubic over its original parameter field. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original cubic inputs construct the literal whole pair's exact H1
rank1; no desired genus or cohomology equality is assumed. -/
theorem smoothCubic_genericPlanePair_unit_cohomology_one_finite_finrank_eq_one
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
        (SheafOfModules.unit X.ringCatSheaf) 1) = 1 := by
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
  exact smoothCubicLinearPair_unit_cohomology_one_finite_finrank_eq_one
    pL (genericHyperplaneEquation (K := K)) hpL hpL0
    genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero

private theorem unitH1_nontrivial_of_schemeIso161
    {X Y : Scheme.{u}} (pi : Y ⟶ Spec (CommRingCat.of K)) (e : X ≅ Y)
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (hY : Nontrivial (schemeModuleCohomology Y
      (SheafOfModules.unit Y.ringCatSheaf) 1)) :
    Nontrivial (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) := by
  letI : Nontrivial (schemeModuleCohomology Y
      (SheafOfModules.unit Y.ringCatSheaf) 1) := hY
  letI : Linear K Y.Modules := schemeModulesLinearOver pi
  letI : Linear K X.Modules := schemeModulesLinearOver (e.hom ≫ pi)
  let f := (schemeModuleCohomologyIsoLinearEquivOver pi
      (PfaffianDescent.schemeIsoPushforwardUnitIso e) 1).toLinearMap.comp
    (closedImmersion_cohomologyOneLinearMap pi e.hom
      (SheafOfModules.unit X.ringCatSheaf))
  have hSurj : Function.Surjective f :=
    (schemeModuleCohomologyIsoLinearEquivOver pi
        (PfaffianDescent.schemeIsoPushforwardUnitIso e) 1).surjective.comp
      (closedImmersion_cohomologyOneLinearMap_surjective pi e.hom
        (SheafOfModules.unit X.ringCatSheaf))
  exact hSurj.nontrivial

private theorem nontrivial_of_finrank_one161
    (V : Type u) [AddCommGroup V] [Module K V]
    (h : Module.finrank K V = 1) : Nontrivial V :=
  Module.nontrivial_of_finrank_eq_succ (R := K) (M := V) (n := 0) h

private theorem finite_finrank_one_of_nontrivial_bound161
    (V : Type u) [AddCommGroup V] [Module K V]
    (hFinite : Module.Finite K V) (hBound : Module.finrank K V ≤ 1)
    (hNontrivial : Nontrivial V) :
    Module.Finite K V ∧ Module.finrank K V = 1 := by
  letI : Module.Finite K V := hFinite
  letI : Nontrivial V := hNontrivial
  have hPos : 0 < Module.finrank K V := Module.finrank_pos
  exact ⟨hFinite, Nat.le_antisymm hBound (Nat.succ_le_of_lt hPos)⟩

private theorem smoothCubic_actualLinearGenericPlaneSection_unitH1_nontrivial_cut161
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
    Nontrivial (schemeModuleCohomology E
      (SheafOfModules.unit E.ringCatSheaf) 1) := by
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
  letI : Linear L Y.Modules := schemeModulesLinearOver (toBase I)
  have hY := smoothCubic_genericPlanePair_unit_cohomology_one_finite_finrank_eq_one p hp hp0
  have hYNontrivial : Nontrivial (schemeModuleCohomology Y
      (SheafOfModules.unit Y.ringCatSheaf) 1) :=
    nontrivial_of_finrank_one161 (K := L)
      (schemeModuleCohomology Y (SheafOfModules.unit Y.ringCatSheaf) 1) hY.2
  exact unitH1_nontrivial_of_schemeIso161 (toBase I)
    (actualGenericPlanePairSchemeIso p hp) hYNontrivial

/-- The SAME actual rectangular plane cubic has native finite unit H1
with rank1 for its independently original `hypersurfaceToBase` action. -/
theorem smoothCubic_actualLinearGenericPlaneSection_unit_cohomology_one_finite_finrank_eq_one
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
        (SheafOfModules.unit E.ringCatSheaf) 1) = 1 := by
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
  have hE := smoothCubic_actualLinearGenericPlaneSection_unit_cohomology_one_finite_finrank_le_one
    p hp hp0
  exact finite_finrank_one_of_nontrivial_bound161 (K := L)
    (schemeModuleCohomology E (SheafOfModules.unit E.ringCatSheaf) 1)
    hE.1 hE.2
    (smoothCubic_actualLinearGenericPlaneSection_unitH1_nontrivial_cut161 p hp hp0)

end PfaffianDescent.Coray
