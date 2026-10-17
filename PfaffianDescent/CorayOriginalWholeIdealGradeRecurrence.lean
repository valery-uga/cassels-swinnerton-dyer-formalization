import PfaffianDescent.CorayWholeIdealGradeRestriction
import PfaffianDescent.CorayWholeIdealRestrictionHomogeneousKernel
import PfaffianDescent.ProjectiveFiniteOfHilbertBound

/-! Consecutive-degree upper bound for the whole original component ideal
inside the original cubic surface. All restriction/kernel and finiteness
hypotheses of the generic rank lemma are constructed here. SOURCE ONLY. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem surfacePlaneCoordinateRestriction_mem_grade
    (t : Fin 3 → K) (p : MvPolynomial (Fin 4) K) {e : ℕ} (hp : p.IsHomogeneous e)
    (d : ℕ) (x : CoordinateRing (equationIdeal p hp))
    (hx : x ∈ grading (equationIdeal p hp) d) :
    surfacePlaneCoordinateRestriction t p hp x ∈
      grading (equationIdeal (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp)) d := by
  obtain ⟨q, hq, hqx⟩ := hx
  rw [← hqx]
  change surfacePlaneCoordinateRestriction t p hp
    (Ideal.Quotient.mk (equationIdeal p hp).toIdeal q) ∈ _
  rw [surfacePlaneCoordinateRestriction_mk]
  exact ⟨planeHyperplaneRestrictionHom t q,
    planeHyperplaneRestrictionHom_homogeneous t q hq, rfl⟩

theorem wholeIdealGrade_finite_of_grade_finite
    {A : Type*} [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) (J : Ideal A) (d : ℕ)
    [Module.Finite K (G d)] : Module.Finite K (wholeIdealGrade G J d) := by
  let i : wholeIdealGrade G J d →ₗ[K] G d :=
    Submodule.inclusion (show wholeIdealGrade G J d ≤ G d from inf_le_right)
  exact Module.Finite.of_injective i (Submodule.inclusion_injective _)

abbrev wholeOriginalSurfaceIdealGrade
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d : ℕ) :=
  wholeIdealGrade
    (grading (equationIdeal (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)))
    (wholeOriginalSurfaceCoordinateIdeal C p hp) d

abbrev wholeOriginalPlaneCutIdealGrade
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d : ℕ) :=
  wholeIdealGrade
    (grading (equationIdeal
      (planeHyperplaneRestrictionHom (genericHyperplaneCoefficient (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))))
      (planeHyperplaneRestrictionHom_homogeneous (genericHyperplaneCoefficient (K := K))
        _ (hp.map _))))
    (wholeOriginalPlaneCutCoordinateIdeal C p hp) d

/-- The original p/q/minimal-component input gives a genuine ideal Hilbert
function inequality. The target is the same whole plane-cut ideal, not its
radical or only a closed subscheme with the same support. -/
theorem selectedOriginalWholeCurve_wholeIdealGrade_finrank_recurrence_le
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (d : ℕ) :
    finrank (GenericHyperplaneField K) (wholeOriginalSurfaceIdealGrade C p hp (d + 1)) ≤
      finrank (GenericHyperplaneField K) (wholeOriginalSurfaceIdealGrade C p hp d) +
        finrank (GenericHyperplaneField K) (wholeOriginalPlaneCutIdealGrade C p hp (d + 1)) := by
  classical
  let F := GenericHyperplaneField K
  let t := genericHyperplaneCoefficient (K := K)
  let f := p.map (algebraMap K F)
  let hf := hp.map (algebraMap K F)
  let I := equationIdeal f hf
  let P := equationIdeal (planeHyperplaneRestrictionHom t f)
    (planeHyperplaneRestrictionHom_homogeneous t f hf)
  let J := wholeOriginalSurfaceCoordinateIdeal C p hp
  let Q := wholeOriginalPlaneCutCoordinateIdeal C p hp
  let r := surfacePlaneCoordinateRestriction t f hf
  let H := Ideal.Quotient.mk I.toIdeal (genericHyperplaneEquation (K := K))
  letI : ∀ a, Module.Finite F (grading I a) := PfaffianDescent.polynomialQuotientGrade_finite I
  letI : ∀ a, Module.Finite F (grading P a) := PfaffianDescent.polynomialQuotientGrade_finite P
  letI : Module.Finite F (wholeIdealGrade (grading I) J d) :=
    wholeIdealGrade_finite_of_grade_finite (grading I) J d
  letI : Module.Finite F (wholeIdealGrade (grading I) J (d + 1)) :=
    wholeIdealGrade_finite_of_grade_finite (grading I) J (d + 1)
  letI : Module.Finite F (wholeIdealGrade (grading P) Q (d + 1)) :=
    wholeIdealGrade_finite_of_grade_finite (grading P) Q (d + 1)
  have hdegree : ∀ a x, x ∈ grading I a → r x ∈ grading P a :=
    surfacePlaneCoordinateRestriction_mem_grade t f hf
  have hlanding : ∀ x, x ∈ J → r x ∈ Q := by
    intro x hx
    exact wholeOriginalSurfaceCoordinateIdealRestriction_mem_planeCut C p hp ⟨x, hx⟩
  have hkernel : ∀ y, y ∈ J → r y = 0 → ∃ z, z ∈ J ∧ H * z = y := by
    intro y hy hzero
    let yJ : J.restrictScalars F := ⟨y, hy⟩
    have hker := selectedOriginalWholeCurve_surfacePlaneIdealRestriction_ker_eq_hyperplane_range
      p q hp hp0 n hq hnot C hCmin
    have hyrange : yJ ∈ LinearMap.range
        (wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication C p hp) := by
      rw [← hker]
      exact LinearMap.mem_ker.mpr hzero
    obtain ⟨z, hzy⟩ := LinearMap.mem_range.mp hyrange
    exact ⟨z.val, z.property, congrArg Subtype.val hzy⟩
  have hH : H ∈ grading I 1 := wholeOriginalSurfaceHyperplaneCoordinate_mem_degree_one p hp
  have hrH : r H = 0 := surfacePlaneCoordinateRestriction_hyperplane t f hf
  exact wholeIdealGradeRestriction_finrank_le
    (grading I) (grading P) J Q (wholeOriginalSurfaceCoordinateIdeal_isHomogeneous C p hp)
    r hdegree hlanding H hH hrH hkernel d

end PfaffianDescent.Coray
