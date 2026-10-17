import PfaffianDescent.CorayRankOneSectionCokernelClosedSupport
import PfaffianDescent.CorayIntegralCurveClosedSupportFinite
import PfaffianDescent.CorayNormalizationNonzeroSignedWordGenericStalk
import PfaffianDescent.CorayProjectiveNormalizationStalkDimension
import PfaffianDescent.CorayNormalizationSignedPointTensorWordClosedPointReconstruction

/-! Finite closed support of the SAME original nonzero signed-word
section cokernel on the SAME canonical normalization of the literal
projective p/q curve. Nonzero is an explicit given-section hypothesis.
No existence, support, dimension, constants or degree certificate.
SOURCE ONLY / UNVERIFIED: root alone compiles and audits. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- For a GIVEN actual nonzero signed-word section, the SAME original
categorical cokernel is supported on a finite closed set of actual
closed points. Original rank-one charts, generic-stalk vanishing,
Noetherianity and dimension at most one are derived internally. This
does not yet compute stalk lengths or construct a weighted zero cycle. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_stalkSupport_finite_closed
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
        let Q := cokernel (schemeModuleTopSectionHom W s)
        IsClosed (schemeModuleStalkSupport Q) ∧
        (schemeModuleStalkSupport Q).Finite ∧
        ∀ x ∈ schemeModuleStalkSupport Q, IsClosed ({x} : Set N) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  letI : IsLocallyNoetherian N := integralGenericNormalization_isLocallyNoetherian X (toBase I)
  letI : CompactSpace N := integralGenericNormalization_compactSpace X
  letI : IsNoetherian N :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hdim : ∀ x : N, Ring.DimensionLEOne (N.presheaf.stalk x) :=
    projectiveIntersection_genericNormalization_stalk_dimensionLEOne p q hp hp0 n hq hnot
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
  intro s hs
  let φ := schemeModuleTopSectionHom W s
  let Q := (show N.Modules from cokernel φ)
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    schemeModuleUnitHom_cokernel_stalkSupport_isClosed W hW φ
  have hgeneric : Subsingleton ((Scheme.Modules.presheaf (X := N) Q).stalk (genericPoint N)) :=
    (projectiveIntersection_genericNormalization_nonzeroSignedWordSection_genericStalk_isIso_and_cokernel_isZero
      p q hp hp0 n hn hq hnot ops s hs).2.2
  have hg : genericPoint N ∉ schemeModuleStalkSupport Q := by
    change ¬ Nontrivial ((Scheme.Modules.presheaf (X := N) Q).stalk (genericPoint N))
    exact not_nontrivial_iff_subsingleton.mpr hgeneric
  exact ⟨hclosed, integralCurve_closed_avoiding_generic_finite_and_closedPoints
    N hdim (schemeModuleStalkSupport Q) hclosed hg⟩

end PfaffianDescent.Coray
