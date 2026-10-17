import PfaffianDescent.SchemeModuleNonzeroTopSectionMono
import PfaffianDescent.SchemeModuleCanonicalSignedPointTensorWord
import PfaffianDescent.CorayNormalizationClosedPointIdealRankOne
import PfaffianDescent.CorayNormalizationClosedPointNongeneric

/-! A GIVEN actual nonzero section of the original signed word defines
its actual monic unit map and its actual cokernel short exact sequence on
SAME literal p/q normalization. Rank-one geometry and the canonical frame
are internally derived from original geometry. This conditional statement
does not prove existence of a nonzero section or construct a zero cycle.
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

/-- The actual SAME signed-word section, with its nonzero hypothesis
EXPLICIT, gives O_N -> W -> cokernel as a genuine short exact sequence.
No section existence, zero-support finiteness, stalk length, cycle degree,
normalization-constants equality, or RR conclusion is assumed or proved. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_shortExact
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
        Mono (schemeModuleTopSectionHom W s) ∧
          (ShortComplex.cokernelSequence (schemeModuleTopSectionHom W s)).ShortExact := by
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
  exact schemeModuleTopSectionHom_mono_and_cokernelSequence_shortExact pi W hW C hgC eW s hs

end PfaffianDescent.Coray
