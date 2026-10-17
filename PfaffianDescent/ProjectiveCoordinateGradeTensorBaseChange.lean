import PfaffianDescent.ProjectiveCoordinateTensorBaseChange
import PfaffianDescent.ProjectiveSurjectiveCoefficientGrade
import PfaffianDescent.VoisinGenericFreenessProjectiveModel

/-!
# Degreewise coordinate base change without flatness

The full coordinate-ring tensor equivalence restricts to a map from the
tensor product of each homogeneous piece to the corresponding piece after
coefficient change. The source piece is a direct summand, so this map is
injective even for a non-flat coefficient change. For a surjective
coefficient map it is also surjective, giving the residue-field comparison.
-/

namespace PfaffianDescent

open TensorProduct MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
variable (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
variable (hJC : J.toIdeal.map (MvPolynomial.map (algebraMap R S)) = C.toIdeal)

private noncomputable def gradeTensorToCoordinate (n : ℕ) :
    S ⊗[R] grading J n →ₗ[S] CoordinateRing C :=
  (coordinateRingTensorAlgEquiv J C hJC).toLinearEquiv.toLinearMap.comp
    (AlgebraTensorModule.lTensor S S (grading J n).subtype)

private theorem gradeTensorToCoordinate_mem (n : ℕ)
    (z : S ⊗[R] grading J n) :
    gradeTensorToCoordinate J C hJC n z ∈ grading C n := by
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy =>
      simpa only [map_add] using add_mem hx hy
  | tmul a x =>
      have he : gradeTensorToCoordinate J C hJC n (a ⊗ₜ x) =
          a • coordinateCoefficientMap (algebraMap R S) J C hJC
            (x : CoordinateRing J) := by
        change (coordinateRingTensorAlgEquiv J C hJC)
          (a ⊗ₜ[R] (x : CoordinateRing J)) = _
        calc
          (coordinateRingTensorAlgEquiv J C hJC)
              (a ⊗ₜ[R] (x : CoordinateRing J)) =
              (coordinateRingTensorAlgEquiv J C hJC)
                (a • (1 ⊗ₜ[R] (x : CoordinateRing J))) := by
                  congr 1
                  simp [smul_tmul']
          _ = a • (coordinateRingTensorAlgEquiv J C hJC)
                (1 ⊗ₜ[R] (x : CoordinateRing J)) :=
              (coordinateRingTensorAlgEquiv J C hJC).toLinearEquiv.map_smul a _
          _ = _ := by rw [coordinateRingTensorAlgEquiv_one_tmul]
      rw [he]
      exact (grading C n).smul_mem a
        (coordinateCoefficientMap_mem (algebraMap R S) J C hJC x.2)

/-- Scalar extension of an actual homogeneous coordinate piece into the
matching piece of the coefficient-changed coordinate ring. -/
noncomputable def coordinateGradeTensorMap (n : ℕ) :
    S ⊗[R] grading J n →ₗ[S] grading C n :=
  (gradeTensorToCoordinate J C hJC n).codRestrict
    (grading C n) (gradeTensorToCoordinate_mem J C hJC n)

theorem coordinateGradeTensorMap_tmul (n : ℕ) (a : S) (x : grading J n) :
    coordinateGradeTensorMap J C hJC n (a ⊗ₜ x) =
      a • (⟨coordinateCoefficientMap (algebraMap R S) J C hJC
          (x : CoordinateRing J),
        coordinateCoefficientMap_mem (algebraMap R S) J C hJC x.2⟩ : grading C n) := by
  apply Subtype.ext
  change gradeTensorToCoordinate J C hJC n (a ⊗ₜ x) = _
  change (coordinateRingTensorAlgEquiv J C hJC)
    (a ⊗ₜ[R] (x : CoordinateRing J)) = _
  calc
    _ = (coordinateRingTensorAlgEquiv J C hJC)
        (a • (1 ⊗ₜ[R] (x : CoordinateRing J))) := by
          congr 1
          simp [smul_tmul']
    _ = a • (coordinateRingTensorAlgEquiv J C hJC)
        (1 ⊗ₜ[R] (x : CoordinateRing J)) :=
      (coordinateRingTensorAlgEquiv J C hJC).toLinearEquiv.map_smul a _
    _ = _ := by
      rw [coordinateRingTensorAlgEquiv_one_tmul]
      rfl

/-- No relation appears in a homogeneous piece under arbitrary
coefficient change, even when the coefficient map is not flat. -/
theorem coordinateGradeTensorMap_injective (n : ℕ) :
    Function.Injective (coordinateGradeTensorMap J C hJC n) := by
  letI := gradedRing J
  let r : CoordinateRing J →ₗ[R] grading J n :=
    (DFinsupp.lapply n).comp
      (DirectSum.decomposeLinearEquiv (grading J)).toLinearMap
  have hr : r.comp (grading J n).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (DirectSum.decomposeLinearEquiv (grading J)
      (x : CoordinateRing J)) n = x
    rw [DirectSum.decomposeLinearEquiv_apply_coe]
    simp
  have hL : Function.Injective
      (AlgebraTensorModule.lTensor S S (grading J n).subtype) := by
    have hcomp : (r.lTensor S).comp ((grading J n).subtype.lTensor S) =
        LinearMap.id := by
      rw [← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id]
    exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun hcomp⟩
  have hE : Function.Injective (gradeTensorToCoordinate J C hJC n) :=
    (coordinateRingTensorAlgEquiv J C hJC).toLinearEquiv.injective.comp hL
  intro x y hxy
  apply hE
  exact congrArg Subtype.val hxy

/-- For a surjective coefficient map, every homogeneous fibre class is
obtained by tensoring a homogeneous class over the original base. -/
theorem coordinateGradeTensorMap_surjective_of_surjective
    (hf : Function.Surjective (algebraMap R S)) (n : ℕ) :
    Function.Surjective (coordinateGradeTensorMap J C hJC n) := by
  intro y
  obtain ⟨x, hx⟩ := coordinateCoefficientMap_grade_surjective_of_surjective
    (algebraMap R S) hf J C hJC n y
  refine ⟨1 ⊗ₜ[R] x, ?_⟩
  rw [coordinateGradeTensorMap_tmul, one_smul]
  exact hx

/-- A surjective coefficient change identifies each actual homogeneous
component with the scalar extension of the original component. -/
noncomputable def coordinateGradeTensorLinearEquiv_of_surjective
    (hf : Function.Surjective (algebraMap R S)) (n : ℕ) :
    S ⊗[R] grading J n ≃ₗ[S] grading C n :=
  LinearEquiv.ofBijective (coordinateGradeTensorMap J C hJC n)
    ⟨coordinateGradeTensorMap_injective J C hJC n,
      coordinateGradeTensorMap_surjective_of_surjective J C hJC hf n⟩

end PfaffianDescent
