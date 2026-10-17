import PfaffianDescent.CorayGenericNormalizationAffineQuasicoherent
import PfaffianDescent.CorayGenericNormalizationQuotientAffineSections

/-! The actual quotient's actual affine-Spec tilde model, constructed from
quasicoherence and its SAME chart-scalar section comparison. This is an
intermediate toward native stalk comparison, not a D1 endpoint.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original canonical quotient, restricted to the original affine open
and pushed along its actual isoSpec, is the tilde of the actual defect in the
SAME X.functionField. The comparison is constructed, not supplied. -/
def genericNormalizationQuotientSheaf_affineSpecTildeIso
    (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    (Scheme.Modules.pushforward hU.isoSpec.hom).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj (genericNormalizationQuotientSheaf X)) ≅
      tilde (R := CommRingCat.of Γ(X, U))
        (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField)) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  let A := Γ(X, U)
  let P := (Scheme.Modules.pushforward hU.isoSpec.hom).obj
    ((Scheme.Modules.restrictFunctor U.ι).obj (genericNormalizationQuotientSheaf X))
  let G := moduleSpecΓFunctor (R := A)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := A) P) :=
    genericNormalizationQuotientSheaf_affineSpecPushforward_fromTildeGamma_isIso X U hU
  let eSections : G.obj P ≅ ModuleCat.of A (localNormalizationDefect A X.functionField) :=
    affineOpenSpecPushforward_sectionsIso X U hU (genericNormalizationQuotientSheaf X) ≪≫
      genericNormalizationQuotientSheaf_affineSectionsIso X U hU
  exact (asIso (Scheme.Modules.fromTildeΓ (R := A) P)).symm ≪≫
    (tilde.functor (CommRingCat.of A)).mapIso eSections

end PfaffianDescent.Coray
