import PfaffianDescent.ProjectiveCoordinateGradeTensorBaseChange
import PfaffianDescent.VoisinGradedMultiplicationFiberCriterion
import PfaffianDescent.GradedRegularFromPieces
import PfaffianDescent.ProjectiveChartRegularOfCoordinateRegular

/-!
# Multiplication under residue-field graded base change

The degreewise tensor equivalence carries multiplication by a homogeneous
section to multiplication by its coefficient-changed section. Regularity
of that section in a residue-field coordinate ring therefore gives the
residue-field injectivity required by the local graded flatness criterion.
-/

namespace PfaffianDescent

open MvPolynomial
open HomogeneousLocalization
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
variable (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
variable (hJC : J.toIdeal.map (MvPolynomial.map (algebraMap R S)) = C.toIdeal)

/-- The image of a homogeneous equation in the coefficient-changed
homogeneous coordinate algebra. -/
noncomputable def homogeneousCoefficientSection
    {d : ℕ} (s : grading J d) : grading C d :=
  ⟨coordinateCoefficientMap (algebraMap R S) J C hJC
      (s : CoordinateRing J),
    coordinateCoefficientMap_mem (algebraMap R S) J C hJC s.2⟩

/-- The degreewise base-change map commutes with multiplication by a
homogeneous equation. -/
theorem coordinateGradeTensorMap_homogeneousMultiplication
    {d : ℕ} (s : grading J d) (n : ℕ)
    (z : S ⊗[R] grading J n) :
    coordinateGradeTensorMap J C hJC (n + d)
        ((homogeneousMultiplication J s n).lTensor S z) =
      homogeneousMultiplication C (homogeneousCoefficientSection J C hJC s) n
        (coordinateGradeTensorMap J C hJC n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
      simp only [LinearMap.lTensor_tmul, coordinateGradeTensorMap_tmul]
      apply Subtype.ext
      change a • coordinateCoefficientMap (algebraMap R S) J C hJC
          ((x : CoordinateRing J) * (s : CoordinateRing J)) =
        (a • coordinateCoefficientMap (algebraMap R S) J C hJC
          (x : CoordinateRing J)) *
          coordinateCoefficientMap (algebraMap R S) J C hJC
            (s : CoordinateRing J)
      rw [map_mul]
      exact (smul_mul_assoc a _ _).symm

/-- If the changed equation is regular in the actual fibre coordinate
ring, multiplication by the original equation remains injective after
tensoring with the coefficient algebra. No flatness of that algebra is
required. -/
theorem homogeneousMultiplication_lTensor_injective_of_fiber_regular
    {d : ℕ} (s : grading J d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J C hJC s : CoordinateRing C))
    (n : ℕ) :
    Function.Injective ((homogeneousMultiplication J s n).lTensor S) := by
  intro x y hxy
  apply coordinateGradeTensorMap_injective J C hJC n
  apply homogeneousMultiplication_injective_of_isRegular C
    (homogeneousCoefficientSection J C hJC s) hreg n
  calc
    homogeneousMultiplication C (homogeneousCoefficientSection J C hJC s) n
        (coordinateGradeTensorMap J C hJC n x) =
      coordinateGradeTensorMap J C hJC (n + d)
        ((homogeneousMultiplication J s n).lTensor S x) :=
      (coordinateGradeTensorMap_homogeneousMultiplication J C hJC s n x).symm
    _ = coordinateGradeTensorMap J C hJC (n + d)
        ((homogeneousMultiplication J s n).lTensor S y) := congrArg _ hxy
    _ = homogeneousMultiplication C (homogeneousCoefficientSection J C hJC s) n
        (coordinateGradeTensorMap J C hJC n y) :=
      coordinateGradeTensorMap_homogeneousMultiplication J C hJC s n y

/-- When the coefficient map is surjective, injectivity of the tensored
degree map is equivalent to injectivity of multiplication in the actual
coefficient-changed homogeneous piece. -/
theorem homogeneousMultiplication_fiber_injective_of_lTensor_injective
    (hf : Function.Surjective (algebraMap R S))
    {d : ℕ} (s : grading J d) (n : ℕ)
    (hinj : Function.Injective
      ((homogeneousMultiplication J s n).lTensor S)) :
    Function.Injective
      (homogeneousMultiplication C (homogeneousCoefficientSection J C hJC s) n) := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := coordinateGradeTensorMap_surjective_of_surjective
    J C hJC hf n x
  obtain ⟨y', rfl⟩ := coordinateGradeTensorMap_surjective_of_surjective
    J C hJC hf n y
  have hxy' : (homogeneousMultiplication J s n).lTensor S x' =
      (homogeneousMultiplication J s n).lTensor S y' := by
    apply coordinateGradeTensorMap_injective J C hJC (n + d)
    rw [coordinateGradeTensorMap_homogeneousMultiplication,
      coordinateGradeTensorMap_homogeneousMultiplication]
    exact hxy
  exact congrArg (coordinateGradeTensorMap J C hJC n) (hinj hxy')

/-- On a local flat projective model, regularity of the equation in the
actual residue-field coordinate ring implies degreewise injectivity after
reduction by every ideal of the coefficient ring. -/
theorem homogeneousMultiplication_allIdeal_injective_of_residue_regular
    {T : Type u} [CommRing T] [IsLocalRing T]
    (J₀ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J₀)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J₀.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    {d : ℕ} (s₀ : grading J₀ d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J₀ C₀ hJC₀ s₀ : CoordinateRing C₀))
    (n : ℕ) (I : Ideal T) :
    Function.Injective
      ((homogeneousMultiplication J₀ s₀ n).lTensor (T ⧸ I)) :=
  homogeneousMultiplication_quotient_injective_of_residueField_injective
    J₀ s₀ n
    (homogeneousMultiplication_lTensor_injective_of_fiber_regular
      J₀ C₀ hJC₀ s₀ hreg n) I

/-- The corresponding quotient of each homogeneous degree is flat over
the local coefficient ring. -/
theorem homogeneousMultiplication_cokernel_flat_of_residue_regular
    {T : Type u} [CommRing T] [IsLocalRing T]
    (J₀ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J₀)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J₀.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    {d : ℕ} (s₀ : grading J₀ d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J₀ C₀ hJC₀ s₀ : CoordinateRing C₀))
    (n : ℕ) :
    Module.Flat T
      ((grading J₀ (n + d)) ⧸ LinearMap.range
        (homogeneousMultiplication J₀ s₀ n)) :=
  homogeneousMultiplication_cokernel_flat_of_residueField_injective
    J₀ s₀ n
    (homogeneousMultiplication_lTensor_injective_of_fiber_regular
      J₀ C₀ hJC₀ s₀ hreg n)

/-- A moving homogeneous equation regular in the residue-field fibre
remains a non-zero-divisor in the **whole** homogeneous coordinate ring
after quotienting the local coefficient ring by any ideal. -/
theorem coordinateRing_allIdealFibre_regular_of_residue_regular
    {T : Type u} [CommRing T] [IsLocalRing T]
    (J₀ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J₀)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J₀.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    {d : ℕ} (s₀ : grading J₀ d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J₀ C₀ hJC₀ s₀ : CoordinateRing C₀))
    (I : Ideal T)
    (Cᵢ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (T ⧸ I)))
    (hJCᵢ : J₀.toIdeal.map
      (MvPolynomial.map (algebraMap T (T ⧸ I))) = Cᵢ.toIdeal) :
    IsRegular
      (homogeneousCoefficientSection J₀ Cᵢ hJCᵢ s₀ : CoordinateRing Cᵢ) := by
  apply coordinateRing_isRegular_of_homogeneousMultiplication_injective
    Cᵢ (homogeneousCoefficientSection J₀ Cᵢ hJCᵢ s₀)
  intro n
  apply homogeneousMultiplication_fiber_injective_of_lTensor_injective
    J₀ Cᵢ hJCᵢ
  · exact Ideal.Quotient.mk_surjective
  · exact homogeneousMultiplication_allIdeal_injective_of_residue_regular
      J₀ C₀ hJC₀ s₀ hreg n I

/-- The same equation is regular on each **actual affine projective chart**
after any coefficient-ideal reduction. -/
theorem chartRing_allIdealFibre_regular_of_residue_regular
    {T : Type u} [CommRing T] [IsLocalRing T]
    (J₀ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    [Module.Flat T (CoordinateRing J₀)]
    (C₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (IsLocalRing.ResidueField T)))
    (hJC₀ : J₀.toIdeal.map
      (MvPolynomial.map (algebraMap T (IsLocalRing.ResidueField T))) = C₀.toIdeal)
    {d : ℕ} (s₀ : grading J₀ d)
    (hreg : IsRegular
      (homogeneousCoefficientSection J₀ C₀ hJC₀ s₀ : CoordinateRing C₀))
    (I : Ideal T)
    (Cᵢ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (T ⧸ I)))
    (hJCᵢ : J₀.toIdeal.map
      (MvPolynomial.map (algebraMap T (T ⧸ I))) = Cᵢ.toIdeal)
    (j : Fin 4) :
    IsRegular (Away.mk (grading Cᵢ) (coordinate_mem Cᵢ j) d
      (homogeneousCoefficientSection J₀ Cᵢ hJCᵢ s₀ : CoordinateRing Cᵢ)
      (by simpa using (homogeneousCoefficientSection J₀ Cᵢ hJCᵢ s₀).2)) := by
  exact chartSection_isRegular_of_coordinateRing_isRegular Cᵢ
    (homogeneousCoefficientSection J₀ Cᵢ hJCᵢ s₀)
    (coordinateRing_allIdealFibre_regular_of_residue_regular
      J₀ C₀ hJC₀ s₀ hreg I Cᵢ hJCᵢ) j

end PfaffianDescent
