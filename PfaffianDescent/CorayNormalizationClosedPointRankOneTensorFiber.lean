import PfaffianDescent.SchemeModuleClosedPointRankOneFiberSequence
import PfaffianDescent.CorayNormalizationClosedPointDualIncrement

/-! Primitive actual tensor geometry on SAME normalization N. The arbitrary
coefficient L has ordinary local rank-one neighborhoods. The point dual and
all actual point/fiber charts are internally derived from original p/q geometry.
The first canonical ideal-tensor kernel is retained literally; its further
evaluation identification with L is a separate map-coherence obligation.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original point dual has actual rank-one neighborhoods on ALL N,
internally from its SAME original regular point ideal and constructed dual. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dual_locallyRankOne
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
      schemeModuleLocallyRankOne (SchemeModuleInternalHom.dual (closedImmersionModule i)) := by
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
  let eM : M.over U.1 ≅ (SheafOfModules.unit N.ringCatSheaf).over U.1 :=
    ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso U.1).symm
  exact ⟨U.1, hxU, ⟨SchemeModuleInternalHom.dualOverUnitIso U.1 eM ≪≫
    (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩

/-- Tensor SAME original increment sequence on the right by a genuine
rank-one L. Original delta, original cokernel projection and actual functor
maps remain; flatness/short exactness are internally derived from local L. -/
theorem projectiveIntersection_genericNormalization_closedPoint_increment_tensor_shortExact
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
      ((SchemeModuleInternalHom.incrementCokernelSequence (closedImmersionModuleToUnit i)).map
        (schemeModuleTensorRight L)).ShortExact := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P L hL
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  exact schemeModuleLocallyRankOne_tensor_shortExact L hL
    (SchemeModuleInternalHom.incrementCokernelSequence (closedImmersionModuleToUnit i))
    (projectiveIntersection_genericNormalization_closedPoint_dualIncrement_shortExact
      p q hp hp0 n hn hq hnot P)

/-- Actual canonical ideal-tensor restriction for T = L tensor D_P.
The original eta_T is the quotient map and uniquely determines its cokernel
Iso. This conclusion retains the literal first object I_P tensor T. -/
theorem projectiveIntersection_genericNormalization_closedPoint_tensorDual_canonical_fiberSequence
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
      let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
      let T := schemeModuleTensor L D
      let S := closedImmersionIdealTwistSequence i T
      let beta := S.f ≫ (schemeModuleTensorUnitLeftIso T).hom
      let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
      ∃ hzero : beta ≫ eta = 0,
        (ShortComplex.mk beta eta hzero).ShortExact ∧
        ∃ E : cokernel beta ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T),
          cokernel.π beta ≫ E.hom = eta ∧
          ∀ F : cokernel beta ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T),
            cokernel.π beta ≫ F = eta → F = E.hom := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P L hL
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  have hD : schemeModuleLocallyRankOne D :=
    projectiveIntersection_genericNormalization_closedPoint_dual_locallyRankOne
      p q hp hp0 n hn hq hnot P
  exact schemeModuleLocallyRankOne_closedPoint_idealTensor_fiberSequence P
    (schemeModuleTensor L D) (schemeModuleLocallyRankOne_tensor L D hL hD)

/-- The SAME intrinsic supported fiber for L tensor D_P has finite original-K
sections of full residue degree. Native Ext and actual finite-type normalization
are internal, and the point frame comes from actual rank-one geometry. -/
theorem projectiveIntersection_genericNormalization_closedPoint_tensorDual_fiberTop_finite_and_finrank
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
    ∀ (P : closedPoints N) (L : N.Modules), schemeModuleLocallyRankOne L →
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let T := schemeModuleTensor L (SchemeModuleInternalHom.dual (closedImmersionModule i))
      Module.Finite K (SchemeModuleOpenSectionsOver pi
        ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T)) ⊤) ∧
        Module.finrank K (SchemeModuleOpenSectionsOver pi
          ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T)) ⊤) =
          pi.residueDegree P.1 := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase I)
  letI : LocallyOfFiniteType pi := inferInstance
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  intro P L hL
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  have hD : schemeModuleLocallyRankOne D :=
    projectiveIntersection_genericNormalization_closedPoint_dual_locallyRankOne
      p q hp hp0 n hn hq hnot P
  exact schemeModuleLocallyRankOne_closedPoint_fiberTop_finite_and_finrank pi P
    (schemeModuleTensor L D) (schemeModuleLocallyRankOne_tensor L D hL hD)

end PfaffianDescent.Coray

