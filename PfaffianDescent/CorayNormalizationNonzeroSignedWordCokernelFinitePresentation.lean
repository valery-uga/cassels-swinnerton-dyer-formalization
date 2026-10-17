import PfaffianDescent.SchemeModuleUnitHomCokernelFinitePresentation
import PfaffianDescent.CorayNormalizationNonzeroSignedWordGenericStalk

/-! For the SAME literal projective p/q normalization and SAME actual
signed-word section, finite presentation and quasicoherence of its actual
cokernel are derived from genuine point-ideal charts. Nonzero is used only
for the actual zero generic stalk, whose prerequisite remains explicitly
the separate generic-stalk source. No support, length, degree, or section
existence certificate is introduced. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual cokernel of a GIVEN nonzero actual signed-word section on
the original normalization is finitely presented and quasicoherent and has
zero generic stalk. All local rank-one geometry is internally derived;
finite closed support and the associated weighted effective cycle remain
separate mathematical obligations. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_finitePresentation_quasicoherent_genericZero
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
        (cokernel (schemeModuleTopSectionHom W s)).IsFinitePresentation ∧
        (cokernel (schemeModuleTopSectionHom W s)).IsQuasicoherent ∧
        Subsingleton ((Scheme.Modules.presheaf (X := N) (cokernel (schemeModuleTopSectionHom W s))).stalk (genericPoint N)) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
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
  have hfinite :=
    schemeModuleTopSectionHom_cokernel_isFinitePresentation_and_isQuasicoherent W hW s
  have hgeneric :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_genericStalk_isIso_and_cokernel_isZero
      p q hp hp0 n hn hq hnot ops s hs
  exact ⟨hfinite.1, hfinite.2, hgeneric.2.2⟩

end PfaffianDescent.Coray
