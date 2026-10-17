import PfaffianDescent.CorayGenericNormalizationPushforwardAffineExt
import PfaffianDescent.SchemeModuleNativeQuasicoherentKernel
import PfaffianDescent.IdealSheafModule

/-! Source-only: the ACTUAL unit pushforward of ANY affine morphism is QC.
This constructs the coefficient needed for the actual component quotient. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine native local quasicoherence of the actual affine-morphism
unit pushforward, recovered from its affine source on every target chart. -/
theorem affineMorphismPushforwardUnit_affineRestrict_isQuasicoherent
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ((Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))).IsQuasicoherent := by
  letI : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  let F := Scheme.Modules.pushforward hU.isoSpec.hom
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))
  let P := F.obj MU
  let N := F.obj ((Scheme.Modules.pushforward (f ∣_ U)).obj
    (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf))
  let C : P ≅ N := F.mapIso (openRestrictPushforwardUnitIso f U)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) N) :=
    affineIsoTargetPushforwardUnit_fromTildeGamma_isIso (f ∣_ U) hU.isoSpec
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) P) :=
    isIso_fromTildeΓ_iff.mpr
      ⟨(moduleSpecΓFunctor (R := Γ(X, U))).obj N,
        ⟨asIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) N) ≪≫ C.symm⟩⟩
  letI : P.IsQuasicoherent := (isQuasicoherent_iff_isIso_fromTildeΓ P).mpr inferInstance
  let A := (Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj P
  have hA : A.IsQuasicoherent := by dsimp only [A]; infer_instance
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorAdjCounitIso hU.isoSpec.hom).app MU) hA

/-- Global QC of the literal unit pushforward is constructed on a genuine
native affine cover, without an assumed pushforward-QC comparison. -/
theorem affineMorphismPushforwardUnit_isQuasicoherent
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] :
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent := by
  let ι := X.affineOpens
  let U : ι → X.Opens := fun j => j.1
  have hU : (⨆ j, U j) = ⊤ := iSup_affineOpens_eq_top X
  have hAffine (j : ι) : IsAffineOpen (U j) := j.2
  let M := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)
  let R : ι → CommRingCat.{u} := fun j => Γ(X, U j)
  let e : ∀ j, (U j : Scheme) ≅ Spec (R j) := fun j => (hAffine j).isoSpec
  letI : ∀ j, ((Scheme.Modules.pullback ((e j).inv ≫ (U j).ι)).obj M).IsQuasicoherent :=
    fun j => by
      let MU := (Scheme.Modules.restrictFunctor (U j).ι).obj M
      letI : MU.IsQuasicoherent :=
        affineMorphismPushforwardUnit_affineRestrict_isQuasicoherent f (U j) (hAffine j)
      let N := (Scheme.Modules.restrictFunctor (e j).inv).obj MU
      have hN : N.IsQuasicoherent := by dsimp only [N]; infer_instance
      let q := (e j).inv ≫ (U j).ι
      let E := (Scheme.Modules.restrictFunctorComp (e j).inv (U j).ι).app M
      letI : ((Scheme.Modules.restrictFunctor q).obj M).IsQuasicoherent :=
        (SheafOfModules.isQuasicoherent (Spec (R j)).ringCatSheaf).prop_of_iso E.symm hN
      exact (SheafOfModules.isQuasicoherent (Spec (R j)).ringCatSheaf).prop_of_iso
        ((Scheme.Modules.restrictFunctorIsoPullback q).app M) inferInstance
  exact schemeNative_isQuasicoherent_of_nativeAffineCover
    U ((Opens.coversTop_iff (T := X) U).mpr hU) R e M

/-- BOTH the actual closed-subscheme structure quotient and its OWN native
kernel are QC. No smoothness, integrality, Cartier presentation or desired
cohomology/degree bound is required. -/
theorem closedImmersionUnitQuotient_and_kernel_isQuasicoherent
    {Y X : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] :
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent ∧
      (kernel (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).IsQuasicoherent := by
  letI : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent :=
    affineMorphismPushforwardUnit_isQuasicoherent i
  letI : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pushforwardId X).app (SheafOfModules.unit X.ringCatSheaf))
      (affineMorphismPushforwardUnit_isQuasicoherent (𝟙 X))
  exact ⟨inferInstance, schemeNative_kernel_isQuasicoherent
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)⟩

end PfaffianDescent.Coray
