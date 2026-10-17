import PfaffianDescent.CorayAffineMorphismUnitCokernelOpenComparison
import PfaffianDescent.NativeNormalizationResidueMaps
import PfaffianDescent.CorayEntireModelIncidenceCycle
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! Literal unit-cokernel affine sections and SAME B/im(actual f.app U),
with original pi/f>>pi scalar actions. No normalization quotient, support,
finite source quotient or desired comparison is supplied as a hypothesis. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The independently defined native K action equals restriction of the
actual original open-ring action along its genuine coefficient homomorphism. -/
private def nativeOpenSections_groundRestrictIso
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (T : X.Modules) (U : X.Opens) :
    ModuleCat.of K (SchemeModuleOpenSectionsOver pi T U) ≅
      (ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U)).obj
        ((schemeOpenModuleFunctor X U).obj T) := by
  letI : Module Γ(X, U) (T.val.obj (op U)) := (T.val.obj (op U)).isModule
  exact Iso.refl _

/-- Original unit-open functions retain their actual original-K action. -/
private def nativeUnitOpenSections_groundLinearEquiv
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (U : X.Opens) :
    letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
    (ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U)).obj
      ((schemeOpenModuleFunctor X U).obj (SheafOfModules.unit X.ringCatSheaf)) ≃ₗ[K]
      Γ(X, U) := by
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  exact
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }

/-- Actual pushed-unit open functions preserve both original scalar actions.
The coefficient naturality is proved for the SAME f, not postulated. -/
private def nativePushforwardUnitOpenSections_groundLinearEquiv
    {X Y : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (f : Y ⟶ X) (U : X.Opens) :
    letI : Algebra K Γ(Y, f ⁻¹ᵁ U) :=
      (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
    (ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U)).obj
      ((schemeOpenModuleFunctor X U).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))) ≃ₗ[K]
      Γ(Y, f ⁻¹ᵁ U) := by
  letI : Algebra K Γ(Y, f ⁻¹ᵁ U) :=
    (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
  refine
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := ?_ }
  intro c s
  change f.app U (schemeOpenBaseRingHom pi U c) *
      (show Γ(Y, f ⁻¹ᵁ U) from s) =
    schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U) c *
      (show Γ(Y, f ⁻¹ᵁ U) from s)
  rw [originalOpenBaseRingHom_section_naturality]

/-- Genuine native original-K affine comparison for the entire literal unit
cokernel of any affine morphism; both source and quotient actions are original. -/
def unitCokernelSheaf_affineGroundSectionQuotientLinearEquiv
    {X Y : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
    letI : Algebra K Γ(Y, f ⁻¹ᵁ U) :=
      (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
    SchemeModuleOpenSectionsOver pi
      (cokernel (C := X.Modules)
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) U ≃ₗ[K]
      (Γ(Y, f ⁻¹ᵁ U) ⧸ LinearMap.range (originalOpenSectionPullbackAlgHom f pi U).toLinearMap) := by
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  letI : Algebra K Γ(Y, f ⁻¹ᵁ U) :=
    (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
  let G := schemeOpenModuleFunctor X U
  let R := ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U)
  let a := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let sigma := originalOpenSectionPullbackAlgHom f pi U
  let eQ := nativeOpenSections_groundRestrictIso pi (cokernel a) U
  let eA := (nativeUnitOpenSections_groundLinearEquiv pi U).toModuleIso
  let eB := (nativePushforwardUnitOpenSections_groundLinearEquiv pi f U).toModuleIso
  let eSections := R.mapIso (unitCokernelSheaf_affineSectionCokernelIso f U hU) ≪≫
    PreservesCokernel.iso R (G.map a)
  have hc : R.map (G.map a) ≫ eB.hom =
      eA.hom ≫ ModuleCat.ofHom sigma.toLinearMap := by
    apply ModuleCat.hom_ext
    ext s
    rfl
  let eC := cokernel.mapIso (R.map (G.map a)) (ModuleCat.ofHom sigma.toLinearMap)
    eA eB hc
  exact (eQ ≪≫ eSections ≪≫ eC ≪≫
    ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom sigma.toLinearMap)).toLinearEquiv

/-- The constructed K-linear comparison takes the LITERAL sheaf quotient
projection to the LITERAL quotient map B→B/im sigma. No square is supplied. -/
theorem unitCokernelSheaf_affineGroundSectionQuotientLinearEquiv_π
    {X Y : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
    letI : Algebra K Γ(Y, f ⁻¹ᵁ U) :=
      (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
    ∀ b : Γ(Y, f ⁻¹ᵁ U),
      unitCokernelSheaf_affineGroundSectionQuotientLinearEquiv pi f U hU
        (((cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app (op U)) b) =
      (LinearMap.range (originalOpenSectionPullbackAlgHom f pi U).toLinearMap).mkQ b := by
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  letI : Algebra K Γ(Y, f ⁻¹ᵁ U) :=
    (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
  let G := schemeOpenModuleFunctor X U
  let R := ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U)
  let a := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let sigma := originalOpenSectionPullbackAlgHom f pi U
  let eQ := nativeOpenSections_groundRestrictIso pi (cokernel a) U
  let eA := (nativeUnitOpenSections_groundLinearEquiv pi U).toModuleIso
  let eB := (nativePushforwardUnitOpenSections_groundLinearEquiv pi f U).toModuleIso
  let eSections := R.mapIso (unitCokernelSheaf_affineSectionCokernelIso f U hU) ≪≫
    PreservesCokernel.iso R (G.map a)
  have hc : R.map (G.map a) ≫ eB.hom =
      eA.hom ≫ ModuleCat.ofHom sigma.toLinearMap := by
    apply ModuleCat.hom_ext
    ext s
    rfl
  let eC := cokernel.mapIso (R.map (G.map a)) (ModuleCat.ofHom sigma.toLinearMap)
    eA eB hc
  let eRange := ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom sigma.toLinearMap)
  have hSections : R.map (G.map (cokernel.π a)) ≫ eSections.hom =
      cokernel.π (R.map (G.map a)) := by
    change R.map (G.map (cokernel.π a)) ≫
      (R.map (unitCokernelSheaf_affineSectionCokernelIso f U hU).hom ≫
        (PreservesCokernel.iso R (G.map a)).hom) = _
    rw [← Category.assoc, ← R.map_comp,
      unitCokernelSheaf_affineSectionCokernelIso_π,
      PreservesCokernel.π_iso_hom]
  have hMap : cokernel.π (R.map (G.map a)) ≫ eC.hom =
      eB.hom ≫ cokernel.π (ModuleCat.ofHom sigma.toLinearMap) := cokernel.π_desc _ _ _
  have hTotal : R.map (G.map (cokernel.π a)) ≫
      (eSections ≪≫ eC ≪≫ eRange).hom =
      eB.hom ≫ ModuleCat.ofHom (LinearMap.range sigma.toLinearMap).mkQ := by
    simp only [Iso.trans_hom]
    rw [← Category.assoc, ← Category.assoc, hSections, hMap, Category.assoc,
      ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
    rfl
  intro b
  have hb := ConcreteCategory.congr_hom hTotal b
  change unitCokernelSheaf_affineGroundSectionQuotientLinearEquiv pi f U hU
    (((cokernel.π a).val.app (op U)) b) =
      (LinearMap.range sigma.toLinearMap).mkQ b
  exact hb

/-- For the SAME finite coefficient-component map, actual affine sections
of its ENTIRE native unit-cokernel equal local B/im sigma with original K
actions and literal projection. The local producer's sigma is identified by
its already proved actual ring-hom equation, not chosen to satisfy the result. -/
theorem coefficientComponentToOriginal_unitCokernel_affineGroundQuotient_exists_preserving_projection
    {M : Type u} [Field M] [Algebra K M] [Module.Finite K M]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (U : (scheme I).Opens) (hU : IsAffineOpen U) :
    let piI := toBase I
    let f := coefficientComponentToOriginal I D hID
    let piB := f ≫ piI
    let V := f ⁻¹ᵁ U
    let A := Γ(scheme I, U)
    let B := Γ(scheme D, V)
    let a := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
    let Q := cokernel (C := (scheme I).Modules) a
    letI : Algebra K A := (schemeOpenBaseRingHom piI U).toAlgebra
    letI : Algebra K B := (schemeOpenBaseRingHom piB V).toAlgebra
    ∀ sigma : A →ₐ[K] B, sigma.toRingHom = (f.app U).hom →
      ∃ E : SchemeModuleOpenSectionsOver piI Q U ≃ₗ[K]
          (B ⧸ LinearMap.range sigma.toLinearMap),
        ∀ b : B, E (((cokernel.π a).val.app (op U)) b) =
          (LinearMap.range sigma.toLinearMap).mkQ b := by
  let piI := toBase I
  let f := coefficientComponentToOriginal I D hID
  let piB := f ≫ piI
  let V := f ⁻¹ᵁ U
  let A := Γ(scheme I, U)
  let B := Γ(scheme D, V)
  letI : Algebra K A := (schemeOpenBaseRingHom piI U).toAlgebra
  letI : Algebra K B := (schemeOpenBaseRingHom piB V).toAlgebra
  letI : IsFinite f := (coefficientComponentToOriginal_finite_and_toBase I D hID).1
  dsimp only
  intro sigma hsigma
  have hEq : sigma = originalOpenSectionPullbackAlgHom f piI U := by
    apply AlgHom.ext
    intro s
    change sigma s = (f.app U).hom s
    exact DFunLike.congr_fun hsigma s
  subst sigma
  refine ⟨unitCokernelSheaf_affineGroundSectionQuotientLinearEquiv piI f U hU, ?_⟩
  exact unitCokernelSheaf_affineGroundSectionQuotientLinearEquiv_π piI f U hU

end PfaffianDescent.Coray
