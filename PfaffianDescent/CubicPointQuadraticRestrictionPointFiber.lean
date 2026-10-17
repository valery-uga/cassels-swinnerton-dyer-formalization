import PfaffianDescent.CubicPointQuadraticRestrictionContraction
import PfaffianDescent.CanonicalPointRestriction

/-! # Actual closed-point twist fiber and its normalized coordinate

This uses the actual closed-immersion restriction morphism into the tensor
of the direct-image point module with the twist. The coordinate is normalized
against any supplied free coordinate of the ambient twist stalk.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

variable {X : Scheme.{u}} {L : Type u} [Field L]
  (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))

set_option backward.isDefEq.respectTransparency false in
/-- The actual direct-image point stalk has the canonical residue coordinate. -/
def cubicPointQuadraticRestrictionPushforwardResidueIso :
    (schemeModuleStalkModuleFunctor X (i x)).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) ≅
    ModuleCat.of (X.presheaf.stalk (i x))
      ((X.presheaf.stalk (i x)) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) := by
  letI := schemeModuleStalkModule
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) (i x)
  exact LinearEquiv.toModuleIso
    (quotientStalkLinearEquivOfSurjectiveAndKernelEq
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
      (closedImmersionPushforwardStalkFromRingLinearMap i (i x))
      (closedImmersionPushforwardStalkFromRingLinearMap_surjective i (i x))
      (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal i x)).symm

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
theorem cubicPointQuadraticRestrictionPushforwardResidueIso_mk
    (r : X.presheaf.stalk (i x)) :
    (cubicPointQuadraticRestrictionPushforwardResidueIso i x).hom
      (closedImmersionPushforwardStalkFromRingLinearMap i (i x) r) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) r := by
  letI := schemeModuleStalkModule
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) (i x)
  exact quotientStalkLinearEquivOfSurjectiveAndKernelEq_symm_apply
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (closedImmersionPushforwardStalkFromRingLinearMap i (i x))
    (closedImmersionPushforwardStalkFromRingLinearMap_surjective i (i x))
    (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal i x) r

set_option backward.isDefEq.respectTransparency false in
theorem cubicPointQuadraticRestrictionPushforwardResidueIso_unit
    (z : (schemeModuleStalkModuleFunctor X (i x)).obj
      (SheafOfModules.unit X.ringCatSheaf)) :
    (cubicPointQuadraticRestrictionPushforwardResidueIso i x).hom
      ((schemeModuleStalkModuleFunctor X (i x)).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) z) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
      ((schemeModuleUnitStalkIso X (i x)).hom z) := by
  have h := cubicPointQuadraticRestrictionPushforwardResidueIso_mk i x
    ((schemeModuleUnitStalkIso X (i x)).hom z)
  change (cubicPointQuadraticRestrictionPushforwardResidueIso i x).hom
      ((schemeModuleStalkModuleFunctor X (i x)).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)
          ((schemeModuleUnitStalkIso X (i x)).inv
            ((schemeModuleUnitStalkIso X (i x)).hom z))) = _ at h
  rw [Iso.hom_inv_id_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A linear automorphism of the ring preserves every ideal as a submodule. -/
theorem cubicPointQuadraticRestriction_ringIso_mapIdeal
    {R : Type u} [CommRing R] (c : ModuleCat.of R R ≅ ModuleCat.of R R) (J : Ideal R) :
    Submodule.map c.hom.hom (J : Submodule R R) = (J : Submodule R R) := by
  have hJ : (J : Submodule R R) = J • (⊤ : Submodule R R) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  conv_lhs => rw [hJ]
  have hrange : LinearMap.range c.hom.hom = ⊤ :=
    LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso c.hom).2
  rw [Submodule.map_smul'', Submodule.map_top, hrange]
  exact hJ.symm

/-- The actual restriction morphism to the twist of the closed-point module. -/
def cubicPointQuadraticRestrictionToPoint (P : X.Modules) :
    P ⟶ (closedImmersionIdealTwistSequence i P).X₃ :=
  (schemeModuleTensorUnitLeftIso P).inv ≫ (closedImmersionIdealTwistSequence i P).g

variable (U : X.Opens) (hx : i x ∈ U) (P : X.Modules)
  (eP : (SheafOfModules.overFunctor X.ringCatSheaf U).obj P ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver X.sheaf U)))
  (qP : (schemeModuleStalkModuleFunctor X (i x)).obj P ≅
    ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))

/-- The actual closed-point twist fiber has a residue coordinate compatible
with the supplied ambient stalk coordinate. -/
def cubicPointQuadraticRestrictionPointFiberResidueIso :
    (schemeModuleStalkModuleFunctor X (i x)).obj
      (closedImmersionIdealTwistSequence i P).X₃ ≅
    ModuleCat.of (X.presheaf.stalk (i x))
      ((X.presheaf.stalk (i x)) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) := by
  let q₀ := cubicPointQuadraticRestrictionTensorRightCoordinate U ⟨i x, hx⟩ P eP
  let c : ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)) ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)) := q₀.symm ≪≫ qP
  let J := IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))
  exact schemeModuleTensorStalkModuleIsoOfLocalTrivialization U ⟨i x, hx⟩
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) P eP ≪≫
    cubicPointQuadraticRestrictionPushforwardResidueIso i x ≪≫
    LinearEquiv.toModuleIso
      (Submodule.Quotient.equiv J J c.toLinearEquiv
        (cubicPointQuadraticRestriction_ringIso_mapIdeal c J))

set_option backward.isDefEq.respectTransparency false in
/-- The actual point restriction square commutes with the compatible coordinate.
This is an equality for the original closed-immersion morphism on every stalk
element, rather than a new definition of restriction. -/
theorem cubicPointQuadraticRestrictionPointFiberResidueIso_restriction
    (y : (schemeModuleStalkModuleFunctor X (i x)).obj P) :
    (cubicPointQuadraticRestrictionPointFiberResidueIso i x U hx P eP qP).hom
      ((schemeModuleStalkModuleFunctor X (i x)).map
        (cubicPointQuadraticRestrictionToPoint i P) y) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) (qP.hom y) := by
  let Q := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let S := schemeModuleStalkModuleFunctor X (i x)
  let t (M : X.Modules) :=
    schemeModuleTensorStalkModuleIsoOfLocalTrivialization U ⟨i x, hx⟩ M P eP
  let q₀ := cubicPointQuadraticRestrictionTensorRightCoordinate U ⟨i x, hx⟩ P eP
  let c : ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)) ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)) := q₀.symm ≪≫ qP
  let J := IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))
  have hn := cubicPointQuadraticRestrictionTensorStalk_naturality U ⟨i x, hx⟩ P eP
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)
  have hn' : S.map (schemeModuleTensorMap
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) (𝟙 P)) ≫
      (t Q).hom = (t O).hom ≫
      S.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) := hn
  have hbase : (cubicPointQuadraticRestrictionPushforwardResidueIso i x).hom
      ((t Q).hom (S.map (cubicPointQuadraticRestrictionToPoint i P) y)) =
      Ideal.Quotient.mk J (q₀.hom y) := by
    unfold cubicPointQuadraticRestrictionToPoint
    rw [S.map_comp]
    change (S.map (schemeModuleTensorUnitLeftIso P).inv ≫
      S.map (schemeModuleTensorMap
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) (𝟙 P)) ≫
      (t Q).hom ≫ (cubicPointQuadraticRestrictionPushforwardResidueIso i x).hom) y = _
    rw [← Category.assoc (S.map (schemeModuleTensorMap
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) (𝟙 P)))
      (t Q).hom, hn']
    change (cubicPointQuadraticRestrictionPushforwardResidueIso i x).hom
      (S.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)
        ((t O).hom (S.map (schemeModuleTensorUnitLeftIso P).inv y))) = _
    rw [cubicPointQuadraticRestrictionPushforwardResidueIso_unit]
    rfl
  change (Submodule.Quotient.equiv J J c.toLinearEquiv
      (cubicPointQuadraticRestriction_ringIso_mapIdeal c J))
        ((cubicPointQuadraticRestrictionPushforwardResidueIso i x).hom
          ((t Q).hom (S.map (cubicPointQuadraticRestrictionToPoint i P) y))) = _
  rw [hbase]
  change Ideal.Quotient.mk J (qP.hom (q₀.inv (q₀.hom y))) = _
  rw [Iso.hom_inv_id_apply]

end PfaffianDescent
