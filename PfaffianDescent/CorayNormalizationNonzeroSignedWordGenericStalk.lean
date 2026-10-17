import PfaffianDescent.SchemeModuleNonzeroTopSectionGenericStalk
import PfaffianDescent.SchemeModuleCanonicalSignedPointTensorWord
import PfaffianDescent.CorayNormalizationClosedPointIdealRankOne
import PfaffianDescent.CorayNormalizationClosedPointNongeneric

/-! On SAME literal p/q normalization, the original unit map of a GIVEN
nonzero actual signed-word section is invertible on the native generic
stalk and its actual categorical cokernel has zero generic stalk.
All rank-one/common-frame geometry is derived internally. This remains
conditional on the given section, without existence, finite support,
local-length or cycle-degree claims. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original given-nonzero signed-word section is an isomorphism
on the actual generic stalk. Its original categorical cokernel has zero
native module stalk and a subsingleton literal additive stalk. Nonzero
section existence and finite-support/degree conclusions stay separate. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_genericStalk_isIso_and_cokernel_isZero
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ s : W.val.obj (op ⊤), s ≠ 0 →
        IsIso ((schemeModuleStalkModuleFunctor N (genericPoint N)).map
          (schemeModuleTopSectionHom W s)) ∧
        IsZero ((schemeModuleStalkModuleFunctor N (genericPoint N)).obj
          (cokernel (schemeModuleTopSectionHom W s))) ∧
        Subsingleton ((Scheme.Modules.presheaf (X := N) (cokernel (schemeModuleTopSectionHom W s))).stalk (genericPoint N)) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro ops
  have hM : ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i) := by
    intro P
    dsimp only
    let i := N.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show N.Modules from closedImmersionModule i)
    intro x
    obtain ⟨U, hxU, m, hm, _hregular, _hprincipal⟩ :=
      projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
        p q hp hp0 n hn hq hnot P x
    letI := hm
    let e : SheafOfModules.unit (U.1 : Scheme).ringCatSheaf ≅ M.restrict U.1.ι :=
      asIso (schemeModuleSectionOnOpenHom M U.1 m)
    exact ⟨U.1, hxU, ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩
  let O := (show N.Modules from SheafOfModules.unit N.ringCatSheaf)
  let W := schemeModuleIteratedSignedClosedPointTensor O ops
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  have hW : schemeModuleLocallyRankOne W :=
    schemeModuleIteratedSignedClosedPointTensor_locallyRankOne ops O hM hO
  let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint N :=
    fun operation _ => projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq operation.1
  let C := schemeSignedPointTensorWordComplementOpen ops
  have hgC : genericPoint N ∈ C := schemeSignedPointTensorWordComplementOpen_generic_mem ops hP
  let eW := schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
    (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)
  intro s hs
  have hIso := schemeModuleTopSectionHom_genericStalk_isIso pi W hW C hgC eW s hs
  have hZero := schemeModuleTopSectionHom_cokernel_genericStalk_isZero pi W hW C hgC eW s hs
  refine ⟨hIso, hZero, ?_⟩
  exact ModuleCat.subsingleton_of_isZero hZero

end PfaffianDescent.Coray
