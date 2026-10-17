import PfaffianDescent.CorayNormalizationClosedPointNongeneric
import PfaffianDescent.CubicClosedPointSerreZeroIdealStalk
import Mathlib.LinearAlgebra.Span.Basic

/-! The SAME actual closed-point ideal stalk and original inclusion on the
actual normalization. Native DVR and its regular generator are conclusions
of the primitive p/q caller, never supplied geometric certificates.
SOURCE ONLY / UNVERIFIED. This file proves stalk results, not invertibility. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The range of the ACTUAL closed-point ideal's ACTUAL inclusion on stalks
is the original local ring's maximal ideal. This uses the genuine quotient
kernel and actual short exact ideal sequence, not a kernel certificate. -/
theorem closedPointIdeal_stalk_range_eq_maximalIdeal
    (X : Scheme.{u}) (P : closedPoints X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI := schemeModuleStalkModule
      (show X.Modules from IdealSheafDataModule.closedImmersionModule i) P.1
    LinearMap.range (closedImmersionModuleStalkToRingLinearMap i P.1) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI := schemeModuleStalkModule
    (show X.Modules from IdealSheafDataModule.closedImmersionModule i) P.1
  letI := schemeModuleStalkModule
    (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)) P.1
  have hker := closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal
    i (default : Spec (X.residueField P.1))
  have hkerP : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i P.1) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) := by
    have hpoint : i (default : Spec (X.residueField P.1)) = P.1 :=
      Scheme.fromSpecResidueField_apply P.1 _
    let predicate : X → Prop := fun x =>
      letI := schemeModuleStalkModule
        (show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)) x
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x)
    exact Eq.mp (congrArg predicate hpoint) hker
  exact (closedImmersionModule_stalk_range_eq_ker_from_ring i P.1).trans hkerP

/-- Canonical linear equivalence from the SAME ideal-module stalk to the
actual maximal ideal, induced by the original ideal inclusion. -/
def closedPointIdeal_stalkLinearEquivMaximalIdeal
    (X : Scheme.{u}) (P : closedPoints X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    letI := schemeModuleStalkModule M P.1
    M.presheaf.stalk P.1 ≃ₗ[X.presheaf.stalk P.1]
      IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
  letI := schemeModuleStalkModule M P.1
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  let j := closedImmersionModuleStalkToRingLinearMap i P.1
  exact (LinearEquiv.ofInjective j
    (schemeModuleStalkToRingLinearMap_injective_of_mono
      (IdealSheafDataModule.closedImmersionModuleToUnit i) P.1)).trans
    (LinearEquiv.ofEq _ _ (closedPointIdeal_stalk_range_eq_maximalIdeal X P))

/-- The above canonical equivalence preserves the ACTUAL inclusion value. -/
theorem closedPointIdeal_stalkLinearEquivMaximalIdeal_apply
    (X : Scheme.{u}) (P : closedPoints X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    letI := schemeModuleStalkModule M P.1
    ∀ m : M.presheaf.stalk P.1,
      (closedPointIdeal_stalkLinearEquivMaximalIdeal X P m : X.presheaf.stalk P.1) =
        closedImmersionModuleStalkToRingLinearMap i P.1 m := by
  dsimp only
  intro m
  rfl

/-- Natural generic DVR intermediate. The primitive normalization caller
below discharges this actual DVR hypothesis internally. -/
theorem closedPointIdeal_stalk_exists_regularGenerator_of_isDVR
    (X : Scheme.{u}) (P : closedPoints X)
    [IsDomain (X.presheaf.stalk P.1)]
    [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI := schemeModuleStalkModule
      (show X.Modules from IdealSheafDataModule.closedImmersionModule i) P.1
    ∃ ϖ : X.presheaf.stalk P.1, IsRegular ϖ ∧
      LinearMap.range (closedImmersionModuleStalkToRingLinearMap i P.1) =
        Ideal.span ({ϖ} : Set (X.presheaf.stalk P.1)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk P.1)
  exact ⟨ϖ, isRegular_iff_ne_zero.mpr hϖ.ne_zero,
    (closedPointIdeal_stalk_range_eq_maximalIdeal X P).trans hϖ.maximalIdeal_eq⟩

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- EVERY closed point of the ACTUAL normalization of the SAME literal
positive-degree integral p/q curve has an actual DVR stalk. Nongenericity,
Noetherianity, dimension and normality are derived from original geometry. -/
theorem projectiveIntersection_genericNormalization_closedPoint_stalk_isDVR
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N, IsDiscreteValuationRing (N.presheaf.stalk P.1) := by
  dsimp only
  intro P
  exact projectiveIntersection_genericNormalization_nongeneric_stalk_isDVR
    p q hp hp0 n hq hnot P.1
    (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)

/-- The ACTUAL point-ideal stalk is free on an internally constructed
regular generator. Its original inclusion sends the chosen coefficient r
to r*ϖ in the SAME original local ring; no local-free/evaluation premise. -/
theorem projectiveIntersection_genericNormalization_closedPoint_idealStalk_regularFree
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
      let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
      letI := schemeModuleStalkModule M P.1
      ∃ ϖ : N.presheaf.stalk P.1, IsRegular ϖ ∧
        ∃ e : N.presheaf.stalk P.1 ≃ₗ[N.presheaf.stalk P.1] M.presheaf.stalk P.1,
          ∀ r, closedImmersionModuleStalkToRingLinearMap i P.1 (e r) = r * ϖ := by
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let R := N.presheaf.stalk P.1
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  letI := schemeModuleStalkModule M P.1
  letI : IsDiscreteValuationRing R :=
    projectiveIntersection_genericNormalization_closedPoint_stalk_isDVR p q hp hp0 n hn hq hnot P
  obtain ⟨ϖ, hϖ, hrange⟩ := closedPointIdeal_stalk_exists_regularGenerator_of_isDVR N P
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  let j := closedImmersionModuleStalkToRingLinearMap i P.1
  let E : M.presheaf.stalk P.1 ≃ₗ[R] Ideal.span ({ϖ} : Set R) :=
    (LinearEquiv.ofInjective j
      (schemeModuleStalkToRingLinearMap_injective_of_mono
        (IdealSheafDataModule.closedImmersionModuleToUnit i) P.1)).trans
      (LinearEquiv.ofEq _ _ hrange)
  have hE (m : M.presheaf.stalk P.1) : (E m : R) = j m := rfl
  have hEinv (s : Ideal.span ({ϖ} : Set R)) : j (E.symm s) = s.1 := by
    rw [← hE, E.apply_symm_apply]
  let A : R ≃ₗ[R] Ideal.span ({ϖ} : Set R) :=
    LinearEquiv.toSpanNonzeroSingleton R R ϖ (isRegular_iff_ne_zero.mp hϖ)
  refine ⟨ϖ, hϖ, A.trans E.symm, ?_⟩
  intro r
  change j (E.symm (A r)) = r * ϖ
  rw [hEinv]
  rfl

end PfaffianDescent.Coray
