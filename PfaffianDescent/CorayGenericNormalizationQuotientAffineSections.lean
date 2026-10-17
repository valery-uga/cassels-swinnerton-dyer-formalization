import PfaffianDescent.CorayOriginalOpenSections
import PfaffianDescent.CorayGenericNormalizationQuotientRestriction

/-! Actual global normalization quotient SHEAF sections on an affine open.
STATUS: UNVERIFIED source only. No compiler was run by the author.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- ACTUAL affine sections of the ACTUAL global normalization quotient
SHEAF agree with the cokernel of the ACTUAL original linear section map.
This exactness comparison is constructed from restriction, actual affine
source and target transport, and scalar restriction; it is not a premise. -/
def genericNormalizationQuotientSheaf_affineSectionCokernelIso
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    (schemeOpenModuleFunctor X U).obj (genericNormalizationQuotientSheaf X) ≅
      cokernel ((schemeOpenModuleFunctor X U).map
        (genericNormalizationUnitToPushforwardUnit X)) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Algebra Γ(X, U) Γ((X.fromSpecStalk (genericPoint X)).normalization, ν ⁻¹ᵁ U) :=
    (ν.app U).hom.toAlgebra
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (ν ⁻¹ᵁ U).toScheme := genericNormalization_affinePreimage_isAffine X U hU
  let F := Scheme.Modules.restrictFunctor U.ι
  let T := schemeTopModuleFunctor U.toScheme
  let S := ModuleCat.restrictScalars U.topIso.inv.hom
  let H := T ⋙ S
  let G := schemeOpenModuleFunctor X U
  let E := originalOpenRestrictTopSectionsNatIso X U
  let OX := SheafOfModules.unit X.ringCatSheaf
  let N := (Scheme.Modules.pushforward ν).obj
    (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)
  let q := genericNormalizationUnitToPushforwardUnit X
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  let eUnit := Scheme.Modules.restrictUnitIso U.ι
  let ePush := openRestrictPushforwardUnitIso ν U
  let eA := H.mapIso eUnit.symm ≪≫ E.app OX
  let eB := H.mapIso ePush.symm ≪≫ E.app N
  have hcomp : qU ≫ ePush.inv = eUnit.inv ≫ F.map q := by
    apply (cancel_mono ePush.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hu : F.map q ≫ ePush.hom = eUnit.hom ≫ qU :=
      openRestrictPushforwardUnitIso_unit ν U
    rw [hu]
    simp
  have hc : H.map qU ≫ eB.hom = eA.hom ≫ G.map q := by
    change H.map qU ≫ (H.map ePush.inv ≫ E.hom.app N) =
      (H.map eUnit.inv ≫ E.hom.app OX) ≫ G.map q
    rw [← Category.assoc, ← H.map_comp, hcomp, H.map_comp, Category.assoc]
    have hn : H.map (F.map q) ≫ E.hom.app N = E.hom.app OX ≫ G.map q :=
      E.hom.naturality q
    rw [hn, Category.assoc]
  let eSections := S.mapIso
    (T.mapIso (genericNormalizationQuotientSheaf_restrictIso X U) ≪≫
      affineTargetQuotientSheaf_topCokernelIso (ν ∣_ U)) ≪≫
    PreservesCokernel.iso S (T.map qU)
  exact (E.app (genericNormalizationQuotientSheaf X)).symm ≪≫ eSections ≪≫
    cokernel.mapIso (H.map qU) (G.map q) eA eB hc


/-- ACTUAL affine sections of the ACTUAL canonical normalization quotient
SHEAF equal the literal integral-closure quotient, with ORIGINAL chart scalars.
Every restriction, section-exactness and map comparison is constructed. -/
def genericNormalizationQuotientSheaf_affineSectionsIso
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    (schemeOpenModuleFunctor X U).obj (genericNormalizationQuotientSheaf X) ≅
      ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  let eSections :
      (schemeOpenModuleFunctor X U).obj (genericNormalizationQuotientSheaf X) ≅
      cokernel ((schemeOpenModuleFunctor X U).map
        (genericNormalizationUnitToPushforwardUnit X)) :=
    genericNormalizationQuotientSheaf_affineSectionCokernelIso X U hU
  let eDefect :
      cokernel ((schemeOpenModuleFunctor X U).map
        (genericNormalizationUnitToPushforwardUnit X)) ≅
      ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField) :=
    genericNormalization_affineSectionCokernelIso X U hU
  exact eSections ≪≫ eDefect

/-- The actual global quotient-sheaf section comparison also retains the
ORIGINAL ground action of the original structure morphism. -/
def genericNormalizationQuotientSheaf_groundAffineSectionsIso
    (K : Type u) [CommRing K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let beta : K →+* Γ(X, U) :=
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    (ModuleCat.restrictScalars beta).obj
      ((schemeOpenModuleFunctor X U).obj (genericNormalizationQuotientSheaf X)) ≅
    (ModuleCat.restrictScalars beta).obj
      (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField)) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  let beta : K →+* Γ(X, U) :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  exact (ModuleCat.restrictScalars beta).mapIso
    (genericNormalizationQuotientSheaf_affineSectionsIso X U hU)

end PfaffianDescent.Coray
