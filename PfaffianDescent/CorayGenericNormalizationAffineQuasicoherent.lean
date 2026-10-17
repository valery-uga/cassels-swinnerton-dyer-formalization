import PfaffianDescent.CorayGenericNormalizationQuotientRestriction
import PfaffianDescent.CorayAffineOpenSpecSections

/-! Quasicoherence of the actual normalization quotient on every affine open.
The actual source and target transports are constructed in the imported
modules. No quasicoherence or section comparison is an input, and no
nonemptiness assumption on the affine open is required.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual quotient restricted to U, pushed along the ORIGINAL chart
isomorphism U ≅ Spec Γ(X,U), lies in the tilde essential image. The actual
normalized preimage is affine, and the actual quotient transport is derived.
This includes the empty affine open and its possibly trivial section ring. -/
theorem genericNormalizationQuotientSheaf_affineSpecPushforward_fromTildeGamma_isIso
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U))
      ((Scheme.Modules.pushforward hU.isoSpec.hom).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj
          (genericNormalizationQuotientSheaf X)))) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsAffine (ν ⁻¹ᵁ U).toScheme :=
    genericNormalization_affinePreimage_isAffine X U hU
  let A := Γ(X, U)
  let F := Scheme.Modules.pushforward hU.isoSpec.hom
  let G := moduleSpecΓFunctor (R := A)
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj
    (genericNormalizationQuotientSheaf X)
  let P := F.obj MU
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  let N := F.obj (cokernel qU)
  let C : P ≅ N :=
    F.mapIso (genericNormalizationQuotientSheaf_restrictIso X U)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := A) N) :=
    affineIsoTargetQuotientSheaf_fromTildeGamma_isIso (ν ∣_ U) hU.isoSpec
  change IsIso (Scheme.Modules.fromTildeΓ (R := A) P)
  exact isIso_fromTildeΓ_iff.mpr
    ⟨G.obj N, ⟨asIso (Scheme.Modules.fromTildeΓ (R := A) N) ≪≫ C.symm⟩⟩

/-- The actual restriction to the actual affine open is quasicoherent.
Restriction of its constructed Spec pushforward, followed by the genuine
restriction/pushforward counit, returns the original coefficient sheaf. -/
theorem genericNormalizationQuotientSheaf_affineRestrict_isQuasicoherent
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) :
    ((Scheme.Modules.restrictFunctor U.ι).obj
      (genericNormalizationQuotientSheaf X)).IsQuasicoherent := by
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj
    (genericNormalizationQuotientSheaf X)
  let e := hU.isoSpec
  let P := (Scheme.Modules.pushforward e.hom).obj MU
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) P) :=
    genericNormalizationQuotientSheaf_affineSpecPushforward_fromTildeGamma_isIso X U hU
  letI : P.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ P).mpr inferInstance
  let N := (Scheme.Modules.restrictFunctor e.hom).obj P
  have hN : N.IsQuasicoherent := by
    dsimp [N]
    infer_instance
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app MU) hN

/-- Quasicoherence for the EXACT canonical affine-open morphism used by
the affine section-representer Ext theorem. The coefficient object remains
the actual global normalization quotient, with its original scalar actions. -/
theorem genericNormalizationQuotientSheaf_restrictFromSpec_isQuasicoherent
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) :
    ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
      (genericNormalizationQuotientSheaf X)).IsQuasicoherent := by
  let Q := genericNormalizationQuotientSheaf X
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj Q
  letI : MU.IsQuasicoherent :=
    genericNormalizationQuotientSheaf_affineRestrict_isQuasicoherent X U hU
  let N := (Scheme.Modules.restrictFunctor hU.isoSpec.inv).obj MU
  have hN : N.IsQuasicoherent := by
    dsimp [N]
    infer_instance
  let ec := (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app Q
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    ec.symm hN

end PfaffianDescent.Coray
