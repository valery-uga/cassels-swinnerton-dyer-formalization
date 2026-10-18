import AllCharacteristics.HomogeneousKernelLinearIndependence
import AllCharacteristics.SmoothCubicGenericNoContainedLine
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing

/-! An actual algebraically closed generic target field,
constructed from the cubic cone quotient. Its exact polynomial kernel gives
low-degree avoidance and the homogeneous relation detector needed downstream.
The coefficient field K may itself be the algebraic closure of the field of
the two residual centers. -/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry PfaffianDescent MvPolynomial HomogeneousProjective
universe u

abbrev cubicGenericTargetConeRing
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K) :=
  MvPolynomial (Fin 4) K ⧸ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))

abbrev cubicGenericTargetField
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :=
  AlgebraicClosure (FractionRing (cubicGenericTargetConeRing F))

def cubicGenericTargetEvaluation
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :
    MvPolynomial (Fin 4) K →+* cubicGenericTargetField F :=
  (algebraMap (FractionRing (cubicGenericTargetConeRing F)) (cubicGenericTargetField F)).comp
    ((algebraMap (cubicGenericTargetConeRing F) (FractionRing (cubicGenericTargetConeRing F))).comp
      (Ideal.Quotient.mk (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)))))

def cubicGenericTargetCoefficientMap
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :
    K →+* cubicGenericTargetField F :=
  (cubicGenericTargetEvaluation F).comp MvPolynomial.C

def cubicGenericTargetCoordinates
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :
    Fin 4 → cubicGenericTargetField F :=
  fun i => cubicGenericTargetEvaluation F (MvPolynomial.X i)

theorem cubicGenericTargetCoefficientMap_eq_algebraMap
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :
    cubicGenericTargetCoefficientMap F = algebraMap K (cubicGenericTargetField F) := by
  let A := cubicGenericTargetConeRing F
  let Q := FractionRing A
  ext x
  change algebraMap Q (cubicGenericTargetField F)
      (algebraMap A Q (algebraMap K A x)) = algebraMap K (cubicGenericTargetField F) x
  rw [← IsScalarTower.algebraMap_apply K A Q,
    ← IsScalarTower.algebraMap_apply K Q (cubicGenericTargetField F)]

theorem cubicGenericTargetEvaluation_ker
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :
    RingHom.ker (cubicGenericTargetEvaluation F) =
      Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)) := by
  let A := cubicGenericTargetConeRing F
  let Q := FractionRing A
  unfold cubicGenericTargetEvaluation
  rw [RingHom.ker_comp_of_injective _
    (algebraMap Q (AlgebraicClosure Q)).injective,
    RingHom.ker_comp_of_injective _ (IsFractionRing.injective A Q),
    Ideal.mk_ker]

/-- The constructed target vector retains every polynomial relation exactly,
including nonhomogeneous ones; in particular it detects homogeneous ideals. -/
theorem cubicGenericTarget_eval₂_eq
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime]
    (G : MvPolynomial (Fin 4) K) :
    G.eval₂ (cubicGenericTargetCoefficientMap F) (cubicGenericTargetCoordinates F) =
      cubicGenericTargetEvaluation F G := by
  have h : MvPolynomial.eval₂Hom (cubicGenericTargetCoefficientMap F)
      (cubicGenericTargetCoordinates F) = cubicGenericTargetEvaluation F := by
    apply MvPolynomial.ringHom_ext
    · intro x
      exact MvPolynomial.eval₂_C _ _ _
    · intro i
      exact MvPolynomial.eval₂_X _ _ _
  exact DFunLike.congr_fun h G

theorem cubicGenericTarget_relation_iff
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime]
    (G : MvPolynomial (Fin 4) K) :
    G.eval₂ (cubicGenericTargetCoefficientMap F) (cubicGenericTargetCoordinates F) = 0 ↔
      G ∈ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)) := by
  rw [cubicGenericTarget_eval₂_eq]
  change G ∈ RingHom.ker (cubicGenericTargetEvaluation F) ↔ _
  rw [cubicGenericTargetEvaluation_ker]

theorem cubicGenericTargetCoordinates_on_cubic
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime]
    (c : Cubic K 4) (hc : c.toMvPolynomial = F) :
    (c.map (cubicGenericTargetCoefficientMap F)).eval (cubicGenericTargetCoordinates F) = 0 := by
  have hzero : F.eval₂ (cubicGenericTargetCoefficientMap F) (cubicGenericTargetCoordinates F) = 0 :=
    (cubicGenericTarget_relation_iff F F).mpr (Ideal.subset_span (Set.mem_singleton F))
  have heval : c.toMvPolynomial.eval₂ (cubicGenericTargetCoefficientMap F)
      (cubicGenericTargetCoordinates F) = 0 :=
    (congrArg (fun G : MvPolynomial (Fin 4) K =>
      G.eval₂ (cubicGenericTargetCoefficientMap F) (cubicGenericTargetCoordinates F)) hc).trans hzero
  rw [Cubic.eval_toMvPolynomial] at heval
  exact heval

theorem cubicGenericTarget_lowDegree_ne_zero
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime]
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hGdegree : G.totalDegree ≤ 2) :
    G.eval₂ (cubicGenericTargetCoefficientMap F) (cubicGenericTargetCoordinates F) ≠ 0 := by
  intro hzero
  have hdvd : F ∣ G := Ideal.mem_span_singleton.mp
    ((cubicGenericTarget_relation_iff F G).mp hzero)
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hG
  rw [hF.totalDegree hF0] at hle
  omega

theorem cubicGenericTargetCoordinates_linearIndependent
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :
    letI : Algebra K (cubicGenericTargetField F) := (cubicGenericTargetCoefficientMap F).toAlgebra
    LinearIndependent K (cubicGenericTargetCoordinates F) := by
  letI : Algebra K (cubicGenericTargetField F) := (cubicGenericTargetCoefficientMap F).toAlgebra
  exact linearIndependent_coordinates_of_cubic_kernel F hF hF0
    (cubicGenericTargetEvaluation F) rfl (cubicGenericTargetEvaluation_ker F)

theorem cubicGenericTargetCoordinates_ne_zero
    {K : Type u} [Field K] (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :
    cubicGenericTargetCoordinates F ≠ 0 := by
  intro h
  have hX := cubicGenericTarget_lowDegree_ne_zero F hF hF0
    (MvPolynomial.X (0 : Fin 4)) (MvPolynomial.X_ne_zero 0)
    (by simp : (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) K).totalDegree ≤ 2)
  apply hX
  rw [MvPolynomial.eval₂_X]
  exact congrFun h 0

/-- The actual generic target avoids every contained cubic line, derived
from smoothness and its constructed linear-independent coordinates. -/
theorem cubicGenericTarget_no_contained_line
    {K : Type u} [Field K] [IsAlgClosed K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime]
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∀ d : Fin 4 → cubicGenericTargetField F,
      LinearIndependent (cubicGenericTargetField F) ![cubicGenericTargetCoordinates F, d] →
      ∃ s t : cubicGenericTargetField F,
        (c.map (cubicGenericTargetCoefficientMap F)).eval
          (s • cubicGenericTargetCoordinates F + t • d) ≠ 0 := by
  letI : Algebra K (cubicGenericTargetField F) := (cubicGenericTargetCoefficientMap F).toAlgebra
  exact smoothCubic_generic_no_contained_line_through F hF hF0 c hc
    (cubicGenericTargetCoordinates F) (cubicGenericTargetCoordinates_linearIndependent F hF hF0)

end AllCharacteristics
