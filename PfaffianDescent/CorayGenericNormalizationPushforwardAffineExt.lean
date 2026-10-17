import PfaffianDescent.CorayGenericNormalizationQuotientRestriction
import PfaffianDescent.CorayAffineSourceSpecTransport
import PfaffianDescent.AffineOpenCohomology
import PfaffianDescent.SchemeCoverDegreeZeroAcyclic

/-! Actual local quasicoherence and Ext-acyclicity of ν_*O_normalization.
These are derived from the actual affine normalized preimages. They do not
assert exactness of pushforward on all sheaf modules or flatness of ν.
Empty affine opens are included.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport of the actual pushforward structure module along an actual
affine target isomorphism lies in the tilde essential image. This only uses
the genuine affine-source construction for f followed by the target chart. -/
theorem affineIsoTargetPushforwardUnit_fromTildeGamma_isIso
    {X Y : Scheme.{u}} [IsAffine Y] {R : CommRingCat.{u}}
    (f : Y ⟶ X) (e : X ≅ Spec R) :
    IsIso (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward e.hom).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)))) := by
  let P := (Scheme.Modules.pushforward e.hom).obj
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))
  let N := (Scheme.Modules.pushforward (f ≫ e.hom)).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let C : P ≅ N :=
    (Scheme.Modules.pushforwardComp f e.hom).app (SheafOfModules.unit Y.ringCatSheaf)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R) N) :=
    affineSourcePushforwardUnit_fromTildeGamma_isIso (f ≫ e.hom)
  change IsIso (Scheme.Modules.fromTildeΓ (R := R) P)
  exact isIso_fromTildeΓ_iff.mpr
    ⟨(moduleSpecΓFunctor (R := R)).obj N,
      ⟨asIso (Scheme.Modules.fromTildeΓ (R := R) N) ≪≫ C.symm⟩⟩

/-- The actual normalization pushforward, restricted to an actual affine
open and pushed along its original isoSpec, lies in the tilde image. The
actual affine normalized preimage is derived internally from integral X. -/
theorem genericNormalizationPushforwardUnit_affineSpecPushforward_fromTildeGamma_isIso
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U))
      ((Scheme.Modules.pushforward hU.isoSpec.hom).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj
          ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
            (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf))))) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsAffine (ν ⁻¹ᵁ U).toScheme := genericNormalization_affinePreimage_isAffine X U hU
  let F := Scheme.Modules.pushforward hU.isoSpec.hom
  let P := F.obj ((Scheme.Modules.restrictFunctor U.ι).obj
    ((Scheme.Modules.pushforward ν).obj
      (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)))
  let N := F.obj ((Scheme.Modules.pushforward (ν ∣_ U)).obj
    (SheafOfModules.unit (ν ⁻¹ᵁ U).toScheme.ringCatSheaf))
  let C : P ≅ N := F.mapIso (openRestrictPushforwardUnitIso ν U)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) N) :=
    affineIsoTargetPushforwardUnit_fromTildeGamma_isIso (ν ∣_ U) hU.isoSpec
  change IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) P)
  exact isIso_fromTildeΓ_iff.mpr
    ⟨(moduleSpecΓFunctor (R := Γ(X, U))).obj N,
      ⟨asIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) N) ≪≫ C.symm⟩⟩

/-- Genuine quasicoherence on the actual affine open is recovered by the
actual restriction/pushforward counit of the original chart isomorphism. -/
theorem genericNormalizationPushforwardUnit_affineRestrict_isQuasicoherent
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ((Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
        (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf))).IsQuasicoherent := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj
    ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
      (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf))
  let e := hU.isoSpec
  let P := (Scheme.Modules.pushforward e.hom).obj MU
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) P) :=
    genericNormalizationPushforwardUnit_affineSpecPushforward_fromTildeGamma_isIso X U hU
  letI : P.IsQuasicoherent := (isQuasicoherent_iff_isIso_fromTildeΓ P).mpr inferInstance
  let N := (Scheme.Modules.restrictFunctor e.hom).obj P
  have hN : N.IsQuasicoherent := by dsimp [N]; infer_instance
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app MU) hN

/-- Quasicoherence for the exact fromSpec restriction appearing in the
actual affine-open section-representer Ext theorem. -/
theorem genericNormalizationPushforwardUnit_restrictFromSpec_isQuasicoherent
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
      ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
        (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf))).IsQuasicoherent := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let M := (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
    (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
  letI : MU.IsQuasicoherent := genericNormalizationPushforwardUnit_affineRestrict_isQuasicoherent X U hU
  let N := (Scheme.Modules.restrictFunctor hU.isoSpec.inv).obj MU
  have hN : N.IsQuasicoherent := by dsimp [N]; infer_instance
  let ec := (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app M
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso ec.symm hN

/-- Both actual affine section-representer Ext groups of the actual
normalization pushforward vanish. QC is discharged by the actual charts;
there is no surjectivity, flatness, or pushforward-exactness certificate. -/
theorem genericNormalizationPushforwardUnit_affine_sectionRepresenter_ext_one_and_two_subsingleton
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [HasExt.{u} X.Modules]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    Subsingleton (Ext.{u} (show X.Modules from sectionRepresenter X.ringCatSheaf U)
      ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
        (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)) 1) ∧
    Subsingleton (Ext.{u} (show X.Modules from sectionRepresenter X.ringCatSheaf U)
      ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
        (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)) 2) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  exact sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen_of_restrict U hU _
    (genericNormalizationPushforwardUnit_restrictFromSpec_isQuasicoherent X U hU)

/-- Any family of actual affine opens, finite or infinite, has actual
degree-zero Čech Ext¹-acyclicity into the actual normalization pushforward.
All local Ext hypotheses are proved internally. -/
theorem genericNormalizationPushforwardUnit_affineFamily_degreeZeroExt_one_subsingleton
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [hExt : HasExt.{u} X.Modules]
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0)
      ((Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
        (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)) 1) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let M := (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X)).fromNormalization).obj
    (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : ∀ i, Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from sectionRepresenter X.ringCatSheaf (U i)) M 1) := fun i =>
    (genericNormalizationPushforwardUnit_affine_sectionRepresenter_ext_one_and_two_subsingleton
      X (U i) (hU i)).1
  exact schemeCover_degree_zero_ext_one_subsingleton U M

end PfaffianDescent.Coray
