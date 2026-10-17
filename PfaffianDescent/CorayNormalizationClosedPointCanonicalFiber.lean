import PfaffianDescent.SchemeModuleInternalHomTensorCokernel
import PfaffianDescent.CorayNormalizationClosedPointIdealDualEvaluation

/-! Primitive original p/q normalization caller for the SAME canonical
point increment and the ACTUAL intrinsic dual fiber. Original geometry
internally discharges every ideal chart and dual evaluation/tensor
condition. The increment is killed by the actual adjunction unit, and
its SAME categorical cokernel has a generator-independent CANONICAL
factor to i_*i^*D with the actual projection square. Invertibility of
that factor remains a separate theorem. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME actual increment vanishes in the genuine intrinsic point
fiber, with every chart/evaluation/tensor premise discharged internally
from primitive original p/q geometry. No compatibility certificate. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_fiber_zero
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      SchemeModuleInternalHom.unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)) = 0 := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  have hc := projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
    p q hp hp0 n hn hq hnot P
  let B : N → N.affineOpens := fun x => Classical.choose (hc x)
  have hB (x : N) : x ∈ (B x).1 := (Classical.choose_spec (hc x)).1
  let m (x : N) : M.val.obj (op (B x).1) := Classical.choose ((Classical.choose_spec (hc x)).2)
  have hm (x : N) : IsIso (schemeModuleSectionOnOpenHom M (B x).1 (m x)) :=
    (Classical.choose_spec ((Classical.choose_spec (hc x)).2)).1
  apply SchemeModuleInternalHom.closedImmersionDualIncrement_adjunctionUnit_zero
    i (fun x => (B x).1) hB
  intro x
  letI := hm x
  let e : SheafOfModules.unit ((B x).1 : Scheme.{u}).ringCatSheaf ≅
      M.restrict (B x).1.ι := asIso (schemeModuleSectionOnOpenHom M (B x).1 (m x))
  exact ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit (B x).1 e.symm ≪≫
    (SchemeModuleInternalHom.unitOverIso (B x).1).symm

/-- Actual primitive canonical factor to the intrinsic dual fiber, with
the SAME original categorical projection and SAME actual adjunction
unit. The factor is constructed by the literal cokernel universal
property after the internally proved zero relation above. No chosen
bare residue field or desired fiber Iso is substituted. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_fiber_factor
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      let delta := SchemeModuleInternalHom.unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)
      ∃ F : cokernel delta ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D),
        cokernel.π delta ≫ F = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D := by
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
  let delta := SchemeModuleInternalHom.unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D
  have hz : delta ≫ eta = 0 :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_fiber_zero
      p q hp hp0 n hn hq hnot P
  exact ⟨cokernel.desc delta eta hz, cokernel.π_desc _ _ _⟩

end PfaffianDescent.Coray
