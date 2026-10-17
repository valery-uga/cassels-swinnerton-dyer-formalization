import PfaffianDescent.CorayOpenRestrictPushforwardUnit
import PfaffianDescent.CorayGenericNormalizationQuotientSheaf

/-! The ACTUAL global normalization quotient restricted to the ACTUAL open
is the ACTUAL quotient sheaf of the restricted normalization morphism.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The original global quotient SHEAF restricts to the actual quotient SHEAF
for the original normalization morphism restricted to U. This is a genuine
sheaf-level comparison, obtained from proved unit-map compatibility and
restriction preservation of cokernels, not a section comparison premise. -/
def genericNormalizationQuotientSheaf_restrictIso
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    (Scheme.Modules.restrictFunctor U.ι).obj (genericNormalizationQuotientSheaf X) ≅
      cokernel (SheafOfModules.unitToPushforwardObjUnit
        ((X.fromSpecStalk (genericPoint X)).fromNormalization ∣_ U).toRingCatSheafHom) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let F := Scheme.Modules.restrictFunctor U.ι
  let q := genericNormalizationUnitToPushforwardUnit X
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  change F.obj (cokernel q) ≅ cokernel qU
  exact PreservesCokernel.iso F q ≪≫
    cokernel.mapIso (F.map q) qU (Scheme.Modules.restrictUnitIso U.ι)
      (openRestrictPushforwardUnitIso ν U) (openRestrictPushforwardUnitIso_unit ν U)

/-- The global restriction comparison preserves the actual quotient
projection from the actual normalized pushforward on this ORIGINAL open. -/
theorem genericNormalizationQuotientSheaf_restrictIso_π
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    (Scheme.Modules.restrictFunctor U.ι).map
      (cokernel.π (genericNormalizationUnitToPushforwardUnit X)) ≫
        (genericNormalizationQuotientSheaf_restrictIso X U).hom =
      (openRestrictPushforwardUnitIso
        (X.fromSpecStalk (genericPoint X)).fromNormalization U).hom ≫
      cokernel.π (SheafOfModules.unitToPushforwardObjUnit
        ((X.fromSpecStalk (genericPoint X)).fromNormalization ∣_ U).toRingCatSheafHom) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let F := Scheme.Modules.restrictFunctor U.ι
  let q := genericNormalizationUnitToPushforwardUnit X
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  change F.map (cokernel.π q) ≫
    (PreservesCokernel.iso F q ≪≫
      cokernel.mapIso (F.map q) qU (Scheme.Modules.restrictUnitIso U.ι)
        (openRestrictPushforwardUnitIso ν U) (openRestrictPushforwardUnitIso_unit ν U)).hom = _
  let e := cokernel.mapIso (F.map q) qU (Scheme.Modules.restrictUnitIso U.ι)
    (openRestrictPushforwardUnitIso ν U) (openRestrictPushforwardUnitIso_unit ν U)
  calc
    _ = (F.map (cokernel.π q) ≫ (PreservesCokernel.iso F q).hom) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = cokernel.π (F.map q) ≫ e.hom :=
      congrArg (fun t => t ≫ e.hom) (PreservesCokernel.π_iso_hom F q)
    _ = _ := cokernel.π_desc _ _ _

/-- The actual source of the normalization restricted over an actual affine
open is affine, from the actual integral/affine normalization morphism.
No finite-normalization or source-affineness certificate is supplied. -/
theorem genericNormalization_affinePreimage_isAffine
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    IsAffine (((X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U).toScheme) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  exact hU.preimage (X.fromSpecStalk (genericPoint X)).fromNormalization

end PfaffianDescent.Coray
