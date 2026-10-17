import PfaffianDescent.AffineQCAcyclicity
import PfaffianDescent.AffineOpenCohomology
import PfaffianDescent.SheafModuleOverExtComparison
import PfaffianDescent.VoisinProjectiveSpaceCech
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Noetherian

/-!
# Ext vanishing on the standard affine cover of projective three-space

This file connects affine quasicoherent acyclicity with the over-site Ext
comparison.  It proves that the concrete negative twists have vanishing
degree-one and degree-two Ext from the section representer of every ordered
intersection in the standard four-open Cech nerve.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

namespace PfaffianDescent

universe u

/-- An isomorphism of schemes induces an equivalence of their module
categories, realized by restriction along the inverse isomorphism. -/
noncomputable def schemeModulesEquivalenceOfIsoRestrict
    {X Y : Scheme.{u}} (e : X ≅ Y) : X.Modules ≌ Y.Modules := by
  let F : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor e.inv
  let G : Y.Modules ⥤ X.Modules := Scheme.Modules.restrictFunctor e.hom
  let η : 𝟭 X.Modules ≅ F ⋙ G :=
    (Scheme.Modules.restrictFunctorId (X := X)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.hom e.inv
  let ε : G ⋙ F ≅ 𝟭 Y.Modules :=
    (Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId (X := Y)
  letI : F.IsEquivalence := Functor.IsEquivalence.mk' G η ε
  exact F.asEquivalence

@[simp]
theorem schemeModulesEquivalenceOfIsoRestrict_functor
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (schemeModulesEquivalenceOfIsoRestrict e).functor =
      Scheme.Modules.restrictFunctor e.inv := rfl

set_option linter.style.haveILetI false in
/-- Quasicoherent acyclicity on an arbitrary noetherian affine scheme,
transported from its canonical presentation as a spectrum. -/
theorem affineScheme_quasicoherent_cohomology_one_and_two
    {X : Scheme.{u}} [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)]
    [HasExt.{u} X.Modules]
    (M : X.Modules) [M.IsQuasicoherent] :
    Subsingleton (schemeModuleCohomology X M 1) ∧
      Subsingleton (schemeModuleCohomology X M 2) := by
  let R : CommRingCat.{u} := Γ(X, ⊤)
  let E : X.Modules ≌ (Spec R).Modules :=
    schemeModulesEquivalenceOfIsoRestrict X.isoSpec
  letI : EnoughInjectives X.Modules :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : EnoughInjectives (Spec R).Modules :=
    sheafOfModules_enoughInjectives (Spec R).ringCatSheaf
  letI : HasExt.{u} (Spec R).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1}
      (Spec R).Modules
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : E.functor.Additive :=
    Functor.additive_of_preserves_binary_products E.functor
  let FM : (Spec R).Modules := E.functor.obj M
  letI : FM.IsQuasicoherent := by
    have hqc :
        ((Scheme.Modules.restrictFunctor X.isoSpec.inv).obj M).IsQuasicoherent :=
      inferInstance
    simpa only [FM, E, schemeModulesEquivalenceOfIsoRestrict_functor] using hqc
  letI h₁ : Subsingleton (schemeModuleCohomology (Spec R) FM 1) :=
    affine_quasicoherent_cohomology_one FM
  letI h₂ : Subsingleton (schemeModuleCohomology (Spec R) FM 2) :=
    affine_quasicoherent_cohomology_two FM
  constructor
  · exact ext_subsingleton_of_exact_equivalence_of_isos
      E
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) M
      (show (Spec R).Modules from SheafOfModules.unit (Spec R).ringCatSheaf) FM
      (Scheme.Modules.restrictUnitIso X.isoSpec.inv)
      (Iso.refl _) 1
  · exact ext_subsingleton_of_exact_equivalence_of_isos
      E
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) M
      (show (Spec R).Modules from SheafOfModules.unit (Spec R).ringCatSheaf) FM
      (Scheme.Modules.restrictUnitIso X.isoSpec.inv)
      (Iso.refl _) 2

set_option linter.style.haveILetI false in
/-- If a module becomes the structure sheaf on a noetherian affine open,
then Ext from the object representing sections on that open vanishes in
degrees one and two. -/
theorem sectionRepresenter_ext_one_and_two_subsingleton_of_affineOpen_of_restrictIsoUnit
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ((U : Scheme), ⊤)]
    [HasExt.{u} X.Modules]
    (M : X.Modules)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    Subsingleton
        (Ext.{u}
          (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) ∧
      Subsingleton
        (Ext.{u}
          (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 2) := by
  letI : IsAffine (U : Scheme) := hU
  let E := Scheme.Modules.overEquiv U
  let L : SheafOfModules (X.ringCatSheaf.over U) :=
    SheafOfModules.unit (X.ringCatSheaf.over U)
  let FM : SheafOfModules (X.ringCatSheaf.over U) :=
    (SheafOfModules.overFunctor X.ringCatSheaf U).obj M
  let OU : (U : Scheme).Modules :=
    SheafOfModules.unit (U : Scheme).ringCatSheaf
  letI : EnoughInjectives (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
    sheafOfModules_enoughInjectives (X.ringCatSheaf.over U)
  letI : HasExt.{u} (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1}
      (SheafOfModules.{u} (X.ringCatSheaf.over U))
  letI : EnoughInjectives (U : Scheme).Modules :=
    sheafOfModules_enoughInjectives (U : Scheme).ringCatSheaf
  letI : HasExt.{u} (U : Scheme).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1}
      (U : Scheme).Modules
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : E.functor.Additive :=
    Functor.additive_of_preserves_binary_products E.functor
  letI : OU.IsQuasicoherent := by
    let R : CommRingCat.{u} := Γ((U : Scheme), ⊤)
    let OSpec : (Spec R).Modules :=
      SheafOfModules.unit (Spec R).ringCatSheaf
    letI : OSpec.IsQuasicoherent := by
      exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
        (tildeSelf (R := R)) inferInstance
    let N : (U : Scheme).Modules :=
      (Scheme.Modules.restrictFunctor (U : Scheme).isoSpec.hom).obj OSpec
    have hN : N.IsQuasicoherent := by
      dsimp [N]
      infer_instance
    exact (SheafOfModules.isQuasicoherent (U : Scheme).ringCatSheaf).prop_of_iso
      (Scheme.Modules.restrictUnitIso (U : Scheme).isoSpec.hom) hN
  have hOU :
      Subsingleton (schemeModuleCohomology (U : Scheme) OU 1) ∧
        Subsingleton (schemeModuleCohomology (U : Scheme) OU 2) := by
    exact affineScheme_quasicoherent_cohomology_one_and_two OU
  letI : Subsingleton (schemeModuleCohomology (U : Scheme) OU 1) := hOU.1
  letI : Subsingleton (schemeModuleCohomology (U : Scheme) OU 2) := hOU.2
  have h₁ : Subsingleton (Ext.{u} L FM 1) := by
    exact ext_subsingleton_of_exact_equivalence_of_isos
      E L FM OU OU
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)
      ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e) 1
  have h₂ : Subsingleton (Ext.{u} L FM 2) := by
    exact ext_subsingleton_of_exact_equivalence_of_isos
      E L FM OU OU
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)
      ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e) 2
  exact sectionRepresenter_ext_one_and_two_subsingleton_of_over U M h₁ h₂

end PfaffianDescent

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MvPolynomial
open scoped DirectSum
open DirectSum SetLike

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "S" => MvPolynomial (Fin 4) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option linter.style.haveILetI false in
/-- Projective three-space over a field is locally noetherian. -/
theorem p3_isLocallyNoetherian : IsLocallyNoetherian (Proj PS) := by
  letI : IsScalarTower K (PS 0) S := by
    constructor
    intro x y z
    change (x • (y : S)) * z = x • ((y : S) * z)
    exact smul_mul_assoc x (y : S) z
  letI : Algebra.FiniteType (PS 0) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (PS 0) S
  exact LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero PS)

set_option linter.style.haveILetI false in
/-- Every ordered intersection in the standard four-open Cech nerve has
vanishing degree-one and degree-two Ext from its section representer into
each concrete negative twist. -/
theorem p3NegativeTwistCechInter_sectionRepresenter_ext_one_and_two_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    let U : Scheme.Opens (Proj PS) :=
      ⨅ i, p3StandardOpen (K := K) (f i)
    Subsingleton
        (Ext.{u}
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf U)
          (sheafOfModules PS m) 1) ∧
      Subsingleton
        (Ext.{u}
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf U)
          (sheafOfModules PS m) 2) := by
  let U : Scheme.Opens (Proj PS) :=
    ⨅ i, p3StandardOpen (K := K) (f i)
  have hU : IsAffineOpen U := p3StandardOpen_cech_inter_affine K n f
  letI : IsLocallyNoetherian (Proj PS) := p3_isLocallyNoetherian K
  letI : IsLocallyNoetherian (U : Scheme) := inferInstance
  letI : IsAffine (U : Scheme) := hU
  letI : IsNoetherianRing Γ((U : Scheme), ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top (U : Scheme)⟩
  have hUle : U ≤ p3StandardOpen (K := K) (f 0) := by
    exact iInf_le_of_le (0 : Fin (n + 1)) le_rfl
  let e : (Scheme.Modules.restrictFunctor U.ι).obj
      (sheafOfModules PS m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    p3NegativeTwistOpenIsoUnit K U (f 0) hUle m
  exact
    sectionRepresenter_ext_one_and_two_subsingleton_of_affineOpen_of_restrictIsoUnit
      U hU (sheafOfModules PS m) e

/-- Every ordered intersection in the standard four-open Cech nerve has
vanishing section-representer Ext through degree three into each negative
twist. -/
theorem p3NegativeTwistCechInter_sectionRepresenter_ext_one_two_three_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    let U : Scheme.Opens (Proj PS) :=
      ⨅ i, p3StandardOpen (K := K) (f i)
    Subsingleton
        (Ext.{u}
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf U)
          (sheafOfModules PS m) 1) ∧
      Subsingleton
        (Ext.{u}
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf U)
          (sheafOfModules PS m) 2) ∧
      Subsingleton
        (Ext.{u}
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf U)
          (sheafOfModules PS m) 3) := by
  let U : Scheme.Opens (Proj PS) :=
    ⨅ i, p3StandardOpen (K := K) (f i)
  have hU : IsAffineOpen U := p3StandardOpen_cech_inter_affine K n f
  letI : IsLocallyNoetherian (Proj PS) := p3_isLocallyNoetherian K
  letI : IsAffine (U : Scheme) := hU
  have hUle : U ≤ p3StandardOpen (K := K) (f 0) :=
    iInf_le_of_le (0 : Fin (n + 1)) le_rfl
  let e : (Scheme.Modules.restrictFunctor U.ι).obj
      (sheafOfModules PS m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    p3NegativeTwistOpenIsoUnit K U (f 0) hUle m
  let OU : (U : Scheme).Modules :=
    SheafOfModules.unit (U : Scheme).ringCatSheaf
  have hOU : OU.IsQuasicoherent := by
    let R : CommRingCat.{u} := Γ((U : Scheme), ⊤)
    let OSpec : (Spec R).Modules :=
      SheafOfModules.unit (Spec R).ringCatSheaf
    letI : OSpec.IsQuasicoherent := by
      exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
        (tildeSelf (R := R)) inferInstance
    let N : (U : Scheme).Modules :=
      (Scheme.Modules.restrictFunctor (U : Scheme).isoSpec.hom).obj OSpec
    have hN : N.IsQuasicoherent := by
      dsimp [N]
      infer_instance
    exact (SheafOfModules.isQuasicoherent (U : Scheme).ringCatSheaf).prop_of_iso
      (Scheme.Modules.restrictUnitIso (U : Scheme).isoSpec.hom) hN
  let N : (U : Scheme).Modules :=
    (Scheme.Modules.restrictFunctor U.ι).obj (sheafOfModules PS m)
  have hN : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U : Scheme).ringCatSheaf).prop_of_iso e.symm hOU
  let FN : (Spec Γ(Proj PS, U)).Modules :=
    (Scheme.Modules.restrictFunctor hU.isoSpec.inv).obj N
  have hFN : FN.IsQuasicoherent := by
    dsimp [FN]
    letI : N.IsQuasicoherent := hN
    infer_instance
  have hQC : ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
      (sheafOfModules PS m)).IsQuasicoherent := by
    let ec :=
      (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app
        (sheafOfModules PS m)
    exact (SheafOfModules.isQuasicoherent
      (Spec Γ(Proj PS, U)).ringCatSheaf).prop_of_iso ec.symm hFN
  exact
    sectionRepresenter_ext_one_two_three_subsingleton_of_isAffineOpen_of_restrict
      U hU (sheafOfModules PS m) hQC

end PfaffianDescent.ProjectiveNegativeTwist
