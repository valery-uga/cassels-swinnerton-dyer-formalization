import PfaffianDescent.CorayGenericNormalizationQuotientTildeModel

/-! The actual fromSpec restriction is the actual affine defect's tilde.
SOURCE ONLY / UNVERIFIED. No desired stalk comparison is a premise.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Restricting along the original canonical affine chart gives the tilde
of the SAME chart defect in the SAME global function field. Every chart
transport is an actual pushforward composition or restriction counit. -/
def genericNormalizationQuotientSheaf_fromSpecTildeIso
    (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    (genericNormalizationQuotientSheaf X).restrict hU.fromSpec ≅
      tilde (R := CommRingCat.of Γ(X, U))
        (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField)) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  let Q := genericNormalizationQuotientSheaf X
  let MU := Q.restrict U.ι
  let e := hU.isoSpec
  let P := (Scheme.Modules.pushforward e.hom).obj MU
  let H := Scheme.Modules.pushforward e.inv
  let C : H.obj P ≅ MU :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app MU ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app MU ≪≫
      (Scheme.Modules.pushforwardId U.toScheme).app MU
  let E : MU.restrict e.inv ≅ P :=
    (Scheme.Modules.restrictFunctor e.inv).mapIso C.symm ≪≫
      (Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app P
  exact (Scheme.Modules.restrictFunctorComp e.inv U.ι).app Q ≪≫ E ≪≫
    genericNormalizationQuotientSheaf_affineSpecTildeIso X U hU

end PfaffianDescent.Coray
