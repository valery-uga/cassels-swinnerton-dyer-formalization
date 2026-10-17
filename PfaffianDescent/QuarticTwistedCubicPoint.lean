import PfaffianDescent.QuarticTwistedCubicVeronese
import PfaffianDescent.NormalizedProjectiveClosedPoint
import PfaffianDescent.LinearNormalizedProjectivePoint

/-!
# Rational point of the standard twisted cubic

The standard three-quadric projective twisted cubic contains its coordinate
point `[1 : 0 : 0 : 0]` over every field.  This records that fact as an actual
section of its projective structure morphism.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

/-- The standard projective twisted cubic has a rational section. -/
theorem standardTwistedCubic_has_rational_section :
    ∃ s : Spec (.of K) ⟶ scheme (standardTwistedCubicHomogeneousIdeal (K := K)),
      s ≫ toBase (standardTwistedCubicHomogeneousIdeal (K := K)) = 𝟙 _ := by
  let x : Fin 4 → K := ![1, 0, 0, 0]
  have hx : x 0 = 1 := by simp [x]
  have hI : ∀ p ∈ (standardTwistedCubicHomogeneousIdeal (K := K)).toIdeal,
      p.eval₂ (algebraMap K K) x = 0 := by
    intro p hp
    change p ∈ standardTwistedCubicIdeal K at hp
    change p ∈ RingHom.ker (MvPolynomial.eval₂Hom (algebraMap K K) x)
    apply (Ideal.span_le.mpr ?_) hp
    rintro q ⟨i, rfl⟩
    fin_cases i <;> simp [standardTwistedCubicGenerators, x]
  have hgen : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K K) x) := by
    intro y
    refine ⟨C y, ?_⟩
    simp
  obtain ⟨s, -, hs⟩ := closed_point_of_normalized_coordinates
    (standardTwistedCubicHomogeneousIdeal (K := K)) x 0 hx hI hgen
  refine ⟨s, ?_⟩
  simpa using hs

/-- Every member of the standard twisted-cubic ideal vanishes at the first
standard projective point. -/
lemma standardTwistedCubicIdeal_eval_coordinate_zero
    (p : MvPolynomial (Fin 4) K) (hp : p ∈ standardTwistedCubicIdeal K) :
    p.eval₂ (algebraMap K K) ![1, 0, 0, 0] = 0 := by
  change p ∈ RingHom.ker (MvPolynomial.eval₂Hom (algebraMap K K) ![1, 0, 0, 0])
  apply (Ideal.span_le.mpr ?_) hp
  rintro q ⟨i, rfl⟩
  fin_cases i <;> simp [standardTwistedCubicGenerators]

/-- A projective curve whose homogeneous ideal is carried to the standard
twisted-cubic ideal by an invertible ground-field coordinate change has a
rational section. -/
theorem splitTwistedCubic_has_rational_section
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (hI : I.toIdeal.map (linearSubstitution M).toRingHom = standardTwistedCubicIdeal K) :
    ∃ s : Spec (.of K) ⟶ scheme I, s ≫ toBase I = 𝟙 _ := by
  let v : Fin 4 → K := M.mulVec ![1, 0, 0, 0]
  have hv : v ≠ 0 := by
    intro hvzero
    have hinj : Function.Injective M.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr (M.isUnit_iff_isUnit_det.mpr hM)
    have hzero : (![1, 0, 0, 0] : Fin 4 → K) = 0 := hinj (by simpa [v] using hvzero)
    have h0 : (1 : K) = 0 := by
      simpa using congrFun hzero 0
    exact one_ne_zero h0
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let ell : MvPolynomial (Fin 4) K := C (v j)⁻¹ * X j
  have hell : ell.IsHomogeneous 1 := isHomogeneous_C_mul_X (v j)⁻¹ j
  have hvell : ell.eval₂ (algebraMap K K) v = 1 := by
    simp [ell, hj]
  have heval : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K K) v = 0 := by
    intro p hp
    have hp' : linearSubstitution M p ∈ standardTwistedCubicIdeal K := by
      rw [← hI]
      exact Ideal.mem_map_of_mem _ hp
    have hzero := standardTwistedCubicIdeal_eval_coordinate_zero
      (linearSubstitution M p) hp'
    rw [← MvPolynomial.aeval_def] at hzero
    rw [linearSubstitution_eval] at hzero
    simpa only [MvPolynomial.aeval_def] using hzero
  have hgen : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K K) v) := by
    intro y
    refine ⟨C y, ?_⟩
    simp
  obtain ⟨s, -, hs⟩ :=
    closed_point_of_linear_normalized_coordinates I v ell hell hvell heval hgen
  refine ⟨s, ?_⟩
  simpa using hs

end QuarticNet
end PfaffianDescent
