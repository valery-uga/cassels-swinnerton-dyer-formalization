import PfaffianDescent.CorayGenericNormalizationStalkNormality
import PfaffianDescent.CorayAffineNormalizationQuotientSheaf

/-! Actual canonical global normalization quotient and its original affine map.
The quotient of affine SECTIONS is identified here; sections of the GLOBAL
sheaf cokernel require the additional actual open-restriction comparison.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual global unit map for the canonical generic-point normalization. -/
def genericNormalizationUnitToPushforwardUnit (X : Scheme.{u}) [IsIntegral X] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
        (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  exact SheafOfModules.unitToPushforwardObjUnit
    (X.fromSpecStalk (genericPoint X)).fromNormalization.toRingCatSheafHom

/-- The ACTUAL global projective normalization quotient sheaf, defined by
its exact canonical normalization morphism. No genus conclusion is encoded. -/
def genericNormalizationQuotientSheaf (X : Scheme.{u}) [IsIntegral X] : X.Modules := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  exact cokernel (genericNormalizationUnitToPushforwardUnit X)

/-- Its component is the ORIGINAL actual normalization section-ring map. -/
theorem genericNormalizationUnitToPushforwardUnit_app
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (r : Γ(X, U)) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    Scheme.Modules.Hom.app (X := X)
      (genericNormalizationUnitToPushforwardUnit X) U r =
      (X.fromSpecStalk (genericPoint X)).fromNormalization.app U r := by
  rfl

/-- Strengthen the actual normalized-chart ring equivalence to an equivalence
of ORIGINAL chart algebras. Its scalar compatibility is proved from the
actual fromNormalization_app formula and actual mapIntegralClosure. -/
def genericNormalization_preimageSectionsAlgEquiv
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) X.functionField := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  letI : Algebra Γ(X, U) Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    (f.fromNormalization.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let e : Γ(Spec X.functionField, f ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField :=
    AlgEquiv.ofBijective
      { toRingHom := (integralGenericPointPreimageSectionsIso X U).hom.hom
        commutes' := fun r => by
          exact ConcreteCategory.congr_hom (integralGenericPointPreimageSectionsIso_comp_app X U) r }
      (ConcreteCategory.bijective_of_isIso (integralGenericPointPreimageSectionsIso X U).hom)
  refine { (integralGenericNormalization_preimageSectionsRingEquiv X U hU) with
    commutes' := ?_ }
  intro r
  have hc : f.fromNormalization.app U ≫ (f.normalizationObjIso hU).hom =
      CommRingCat.ofHom
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U))) := by
    rw [Scheme.Hom.fromNormalization_app f hU]
    simp
  have hr : (f.normalizationObjIso hU).hom (f.fromNormalization.app U r) =
      algebraMap Γ(X, U) (integralClosure Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U)) r :=
    ConcreteCategory.congr_hom hc r
  change e.mapIntegralClosure
    ((f.normalizationObjIso hU).hom (f.fromNormalization.app U r)) = _
  rw [hr]
  exact e.mapIntegralClosure.commutes r

/-- The ACTUAL chart section cokernel is the literal integral-closure defect,
as a module over the ORIGINAL chart algebra. This is a quotient of sections;
the distinct comparison with sections of the global sheaf cokernel is not
silently assumed. -/
def genericNormalization_affineSectionCokernelIso
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    cokernel ((genericNormalizationUnitToPushforwardUnit X).val.app (op U)) ≅
      ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  letI : Algebra Γ(X, U) Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    (f.fromNormalization.app U).hom.toAlgebra
  let q := (genericNormalizationUnitToPushforwardUnit X).val.app (op U)
  let e :
      ((Scheme.Modules.pushforward f.fromNormalization).obj
        (SheafOfModules.unit f.normalization.ringCatSheaf)).val.obj (op U) ≅
      ModuleCat.of Γ(X, U) (integralClosure Γ(X, U) X.functionField) :=
    (genericNormalization_preimageSectionsAlgEquiv X U hU).toLinearEquiv.toModuleIso
  let g := ModuleCat.ofHom (Algebra.linearMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))
  have hq : q ≫ e.hom = (Iso.refl (ModuleCat.of Γ(X, U) Γ(X, U))).hom ≫ g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (genericNormalization_preimageSectionsAlgEquiv X U hU)
      (f.fromNormalization.app U r) =
      algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField) r
    exact (genericNormalization_preimageSectionsAlgEquiv X U hU).commutes r
  exact cokernel.mapIso q g (Iso.refl _) e hq ≪≫
    ModuleCat.cokernelIsoRangeQuotient g

/-- The chart comparison preserves the literal quotient projection. -/
theorem genericNormalization_affineSectionCokernelIso_π
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    cokernel.π ((genericNormalizationUnitToPushforwardUnit X).val.app (op U)) ≫
      (genericNormalization_affineSectionCokernelIso X U hU).hom =
      (genericNormalization_preimageSectionsAlgEquiv X U hU).toLinearEquiv.toModuleIso.hom ≫
        ModuleCat.ofHom
          (LinearMap.range (Algebra.linearMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))).mkQ := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  letI : Algebra Γ(X, U) Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    (f.fromNormalization.app U).hom.toAlgebra
  let q := (genericNormalizationUnitToPushforwardUnit X).val.app (op U)
  let e :
      ((Scheme.Modules.pushforward f.fromNormalization).obj
        (SheafOfModules.unit f.normalization.ringCatSheaf)).val.obj (op U) ≅
      ModuleCat.of Γ(X, U) (integralClosure Γ(X, U) X.functionField) :=
    (genericNormalization_preimageSectionsAlgEquiv X U hU).toLinearEquiv.toModuleIso
  let g := ModuleCat.ofHom (Algebra.linearMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))
  have hq : q ≫ e.hom = (Iso.refl (ModuleCat.of Γ(X, U) Γ(X, U))).hom ≫ g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (genericNormalization_preimageSectionsAlgEquiv X U hU)
      (f.fromNormalization.app U r) =
      algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField) r
    exact (genericNormalization_preimageSectionsAlgEquiv X U hU).commutes r
  let e₁ : cokernel q ≅ cokernel g :=
    cokernel.mapIso q g (Iso.refl _) e hq
  let e₂ : cokernel g ≅ ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField) :=
    ModuleCat.cokernelIsoRangeQuotient g
  have h₁ : cokernel.π q ≫ e₁.hom = e.hom ≫ cokernel.π g :=
    cokernel.π_desc _ _ _
  have h₂ : cokernel.π g ≫ e₂.hom =
      ModuleCat.ofHom
        (LinearMap.range (Algebra.linearMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))).mkQ :=
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom g
  change cokernel.π q ≫ (e₁ ≪≫ e₂).hom =
    e.hom ≫ ModuleCat.ofHom
      (LinearMap.range (Algebra.linearMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))).mkQ
  calc
    cokernel.π q ≫ (e₁ ≪≫ e₂).hom =
        (cokernel.π q ≫ e₁.hom) ≫ e₂.hom :=
      (Category.assoc _ _ _).symm
    _ = (e.hom ≫ cokernel.π g) ≫ e₂.hom :=
      congrArg (fun k => k ≫ e₂.hom) h₁
    _ = e.hom ≫ (cokernel.π g ≫ e₂.hom) :=
      Category.assoc _ _ _
    _ = e.hom ≫ ModuleCat.ofHom
        (LinearMap.range (Algebra.linearMap Γ(X, U) (integralClosure Γ(X, U) X.functionField))).mkQ :=
      congrArg (fun k => e.hom ≫ k) h₂

/-- Actual chart-cokernel comparison over the ORIGINAL ground ring of the
original structure morphism pi. The ground action is its actual chart app,
not an unrelated scalar structure or supplied ground-linearity certificate. -/
def genericNormalization_groundAffineSectionCokernelIso
    (K : Type u) [CommRing K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let beta : K →+* Γ(X, U) :=
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    (ModuleCat.restrictScalars beta).obj
      (cokernel ((genericNormalizationUnitToPushforwardUnit X).val.app (op U))) ≅
    (ModuleCat.restrictScalars beta).obj
      (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField)) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let beta : K →+* Γ(X, U) :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  exact (ModuleCat.restrictScalars beta).mapIso
    (genericNormalization_affineSectionCokernelIso X U hU)

end PfaffianDescent.Coray
