import PfaffianDescent.SchemeModuleClosedPointTensorDualIncrement
import PfaffianDescent.CorayNormalizationClosedPointIdealRankOne

/-! Primitive intrinsic tensor increment on the SAME original normalization.
The actual ideal/dual, tensor(delta) and eta_T are unchanged. Original p/q
geometry derives the ideal rank-one charts and all comparison/exactness input.
No primitive desired map, exactness, quotient or dimension certificate.
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

/-- Primitive rank-one geometry of the SAME original point ideal, with
all charts obtained from its actual regular affine sections. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_locallyRankOne
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i) := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from closedImmersionModule i)
  intro x
  obtain ⟨U, hxU, m, hm, _hreg, _hprincipal⟩ :=
    projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
      p q hp hp0 n hn hq hnot P x
  letI := hm
  let e : SheafOfModules.unit (U.1 : Scheme).ringCatSheaf ≅ M.restrict U.1.ι :=
    asIso (schemeModuleSectionOnOpenHom M U.1 m)
  exact ⟨U.1, hxU, ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
    (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩

/-- The primitive intrinsic L -> L tensor D_P -> i_*i^*(L tensor D_P)
sequence, with SAME actual tensor(delta) and SAME canonical unit projection.
The cokernel Iso is uniquely specified by that actual projection equality.
Only the ordinary geometric local rank-one hypothesis on arbitrary L remains. -/
theorem projectiveIntersection_genericNormalization_closedPoint_tensorDualIncrement_canonical_fiberSequence
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ (P : closedPoints N) (L : N.Modules), schemeModuleLocallyRankOne L →
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from closedImmersionModule i)
      let j := closedImmersionModuleToUnit i
      let T := schemeModuleTensor L (SchemeModuleInternalHom.dual M)
      let deltaL := schemeModuleRankOneTensorDualIncrement j L
      let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
      ∃ hzero : deltaL ≫ eta = 0,
        (ShortComplex.mk deltaL eta hzero).ShortExact ∧
        ∃ E : cokernel deltaL ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T),
          cokernel.π deltaL ≫ E.hom = eta ∧
          ∀ F : cokernel deltaL ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T),
            cokernel.π deltaL ≫ F = eta → F = E.hom := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P L hL
  have hM := projectiveIntersection_genericNormalization_closedPoint_ideal_locallyRankOne
    p q hp hp0 n hn hq hnot P
  exact schemeModuleClosedPointTensorDualIncrement_canonical_fiberSequence P L hM hL

end PfaffianDescent.Coray
