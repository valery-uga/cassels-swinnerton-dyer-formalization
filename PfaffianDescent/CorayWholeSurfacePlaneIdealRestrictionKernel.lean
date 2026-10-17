import PfaffianDescent.CoraySurfacePlaneCoordinateRestriction
import PfaffianDescent.CorayWholeGenericCutImmersion
import PfaffianDescent.CoraySelectedComponentHeightAndRelevance

/-! The SAME entire original component ideal in the SAME surface quotient
has restriction kernel exactly hyperplane multiplication. The original caller
constructs containment, relevance and regularity from its actual minimal C. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal whole component ideal modulo the original cubic equation. -/
def wholeOriginalSurfaceCoordinateIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    Ideal (CoordinateRing (equationIdeal
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _))) :=
  (wholeGenericCurveIdeal C).toIdeal.map
    (Ideal.Quotient.mk (equationIdeal
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)).toIdeal)

/-- The actual restriction is linear for the original parameter-field action. -/
def wholeOriginalSurfaceCoordinateIdealRestriction
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K) →ₗ[GenericHyperplaneField K]
      CoordinateRing (equationIdeal
        (planeHyperplaneRestrictionHom (genericHyperplaneCoefficient (K := K))
          (p.map (algebraMap K (GenericHyperplaneField K))))
        (planeHyperplaneRestrictionHom_homogeneous (genericHyperplaneCoefficient (K := K))
          _ (hp.map _))) :=
  (surfacePlaneCoordinateRestriction (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)).toLinearMap.comp
      ((wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K)).subtype

/-- Multiplication by the SAME generic H on the SAME quotient ideal. -/
def wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K) →ₗ[GenericHyperplaneField K]
      (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K) where
  toFun := fun y =>
    ⟨Ideal.Quotient.mk (equationIdeal
       (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)).toIdeal
        (genericHyperplaneEquation (K := K)) * y.val,
      (wholeOriginalSurfaceCoordinateIdeal C p hp).mul_mem_left _ y.property⟩
  map_add' := by
    intro y z
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' := by
    intro a y
    apply Subtype.ext
    change _ * (a • y.val) = a • (_ * y.val)
    exact mul_smul_comm _ _ _

/-- The literal whole ideal multiplication is killed by the literal restriction. -/
theorem wholeOriginalSurfaceCoordinateIdealRestriction_hyperplane_mul
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (y : (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K)) :
    wholeOriginalSurfaceCoordinateIdealRestriction C p hp
      (wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication C p hp y) = 0 := by
  change surfacePlaneCoordinateRestriction (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
      (Ideal.Quotient.mk (equationIdeal
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)).toIdeal
          (genericHyperplaneEquation (K := K)) * y.val) = 0
  rw [map_mul]
  have hH := surfacePlaneCoordinateRestriction_hyperplane
    (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
  change surfacePlaneCoordinateRestriction (genericHyperplaneCoefficient (K := K))
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
      (Ideal.Quotient.mk (equationIdeal
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)).toIdeal
          (genericHyperplaneEquation (K := K))) = 0 at hH
  rw [hH, zero_mul]

/-- Genuine original prime and point derive the missing ideal-kernel coefficient. -/
theorem wholeOriginalSurfaceCoordinateIdealRestriction_eq_zero_iff
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C)
    (y : (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K)) :
    wholeOriginalSurfaceCoordinateIdealRestriction C p hp y = 0 ↔
      ∃ z : (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars (GenericHyperplaneField K),
        wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication C p hp z = y := by
  constructor
  · intro hy
    let F := GenericHyperplaneField K
    let f := p.map (algebraMap K F)
    let hf := hp.map (algebraMap K F)
    let J := (wholeGenericCurveIdeal C).toIdeal
    let mk := Ideal.Quotient.mk (equationIdeal f hf).toIdeal
    have hymem : y.val ∈ J.map mk := y.property
    obtain ⟨q, hqJ, hqy⟩ :=
      (Ideal.mem_map_iff_of_surjective mk (Ideal.Quotient.mk_surjective)).mp hymem
    have hzq : surfacePlaneCoordinateRestriction (genericHyperplaneCoefficient (K := K))
        f hf (mk q) = 0 := by
      rw [hqy]
      exact hy
    have hpair := (surfacePlaneCoordinateRestriction_mk_eq_zero_iff
      (genericHyperplaneCoefficient (K := K)) f hf q).mp hzq
    have hreg : ∀ b : MvPolynomial (Fin 4) F,
        planeHyperplaneRelation (genericHyperplaneCoefficient (K := K)) * b ∈ J → b ∈ J := by
      intro b hb
      exact wholeGenericHyperplane_regular C hprime P b hb
    obtain ⟨a, b, hbJ, hab⟩ :=
      (regularHyperplane_pairIdeal_mem_iff J f
        (planeHyperplaneRelation (genericHyperplaneCoefficient (K := K)))
        (originalEquation_mem_wholeGenericCurveIdeal C p hpC) hreg q hqJ).mp hpair
    have hbf : mk f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have hrep : mk q = mk (planeHyperplaneRelation (genericHyperplaneCoefficient (K := K)) * b) := by
      rw [← hab, map_add, map_mul, hbf, mul_zero, zero_add]
    let z : (wholeOriginalSurfaceCoordinateIdeal C p hp).restrictScalars F :=
      ⟨mk b, Ideal.mem_map_of_mem mk hbJ⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change mk (planeHyperplaneRelation (genericHyperplaneCoefficient (K := K))) * mk b = y.val
    rw [← map_mul]
    exact hrep.symm.trans hqy
  · rintro ⟨z, hzy⟩
    rw [← hzy]
    exact wholeOriginalSurfaceCoordinateIdealRestriction_hyperplane_mul C p hp z

/-- Exact linear kernel/range identity, not a supplied dimension estimate. -/
theorem wholeOriginalSurfaceCoordinateIdealRestriction_ker_eq_range
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    LinearMap.ker (wholeOriginalSurfaceCoordinateIdealRestriction C p hp) =
      LinearMap.range (wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication C p hp) := by
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  exact wholeOriginalSurfaceCoordinateIdealRestriction_eq_zero_iff C p hp hpC hprime P y

/-- ORIGINAL minimal component hypotheses construct all kernel prerequisites.
No supplied ideal-containment, generic regularity, point, section or dimension
certificate occurs in this original geometric caller. -/
theorem selectedOriginalWholeCurve_surfacePlaneIdealRestriction_ker_eq_hyperplane_range
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    LinearMap.ker (wholeOriginalSurfaceCoordinateIdealRestriction C p hp) =
      LinearMap.range (wholeOriginalSurfaceCoordinateIdealHyperplaneMultiplication C p hp) := by
  classical
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q})
  have hrel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p q hp hp0 n hq hnot C hCmin
  let P := homogeneousPrimeQuotientProjectivePoint C hCmin.isPrime hrel
  exact wholeOriginalSurfaceCoordinateIdealRestriction_ker_eq_range C p hp hpC hCmin.isPrime P

end PfaffianDescent.Coray
