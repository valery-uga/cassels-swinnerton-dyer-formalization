import PfaffianDescent.SchemeModuleClosedPointGenericFunctionField
import PfaffianDescent.CorayNormalizationClosedPointNongeneric

/-! Primitive ORIGINAL-K field-valued injections for the SAME closed-point
ideal and its CONSTRUCTED O-linear dual on the SAME normalization. Actual
nongenericity and rank-one charts are proved internally from original p/q
geometry. No rational frame, map/comparison or injectivity certificate is
an input. No signed-word or complete pole-image classification is asserted.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual primitive point ideal/dual section injections into the SAME
N.functionField. The codomain's K action is induced by the SAME original
pi = nu followed by toBase, independently of both canonical frames.
No HasExt, finiteness, normalization-constant equality or pole certificate.
The hP appearing in the map is INTERNALLY DERIVED, not a primitive input. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_and_dual_toFunctionField_injective
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ P : closedPoints N,
      let hP := projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P
      Function.Injective (schemeModuleClosedPointIdealToFunctionFieldLinearMap pi P hP) ∧
        Function.Injective (schemeModuleClosedPointDualToFunctionFieldLinearMap pi P hP) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from closedImmersionModule i)
  have hP : P.1 ≠ genericPoint N :=
    projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P
  have hM : schemeModuleLocallyRankOne M := by
    intro x
    obtain ⟨U, hxU, m, hm, _hreg, _hprincipal⟩ :=
      projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
        p q hp hp0 n hn hq hnot P x
    letI := hm
    let e : SheafOfModules.unit (U.1 : Scheme).ringCatSheaf ≅ M.restrict U.1.ι :=
      asIso (schemeModuleSectionOnOpenHom M U.1 m)
    exact ⟨U.1, hxU, ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩
  exact ⟨schemeModuleClosedPointIdealToFunctionFieldLinearMap_injective pi P hP hM,
    schemeModuleClosedPointDualToFunctionFieldLinearMap_injective pi P hP hM⟩

end PfaffianDescent.Coray
