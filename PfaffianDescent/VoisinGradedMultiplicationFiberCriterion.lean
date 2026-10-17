import PfaffianDescent.FibrewiseSplitInjection
import PfaffianDescent.VoisinGenericFreenessProjectiveModel
import AllCharacteristics.GradedCoefficientMap

/-!
# Fibrewise criterion for degreewise multiplication in a flat cubic model

The homogeneous pieces of a flat projective coordinate algebra are finite
flat modules. Over a local coefficient ring they are finite free. A moving
homogeneous equation acts between these pieces, and injectivity in the
residue-field fibre then persists after every coefficient-ideal reduction.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective
open IsLocalRing

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Each homogeneous piece of a flat cubic-model coordinate ring is free
over a local coefficient ring. -/
theorem coordinateRing_homogeneousPiece_free_of_local
    {R : Type u} [CommRing R] [IsLocalRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)] (n : ℕ) :
    Module.Free R (grading J n) := by
  letI : Module.Finite R (grading J n) :=
    coordinateRing_homogeneousPiece_finite J n
  letI : Module.Flat R (grading J n) :=
    coordinateRing_homogeneousPiece_flat J n
  exact Module.free_of_flat_of_isLocalRing

/-- Multiplication by a homogeneous equation between two actual graded
pieces of the projective coordinate algebra. -/
noncomputable def homogeneousMultiplication
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    {d : ℕ} (s : grading J d) (n : ℕ) :
    grading J n →ₗ[R] grading J (n + d) where
  toFun x := ⟨(x : CoordinateRing J) * (s : CoordinateRing J),
    SetLike.mul_mem_graded x.2 s.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, add_mul]
  map_smul' r x := by
    apply Subtype.ext
    exact smul_mul_assoc r (x : CoordinateRing J) (s : CoordinateRing J)

/-- A regular homogeneous equation acts injectively on each actual
homogeneous component of the coordinate ring. -/
theorem homogeneousMultiplication_injective_of_isRegular
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    {d : ℕ} (s : grading J d)
    (hs : IsRegular (s : CoordinateRing J)) (n : ℕ) :
    Function.Injective (homogeneousMultiplication J s n) := by
  intro x y hxy
  apply Subtype.ext
  apply hs.right
  exact congrArg Subtype.val hxy

/-- The equation and a homogeneous input can be changed to new
coefficients before or after multiplying in the coordinate ring. -/
theorem coordinateCoefficientMap_homogeneousMultiplication
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hJC : J.toIdeal.map (MvPolynomial.map f) = C.toIdeal)
    {d : ℕ} (s : grading J d) (n : ℕ) (x : grading J n) :
    coordinateCoefficientMap f J C hJC
        ((homogeneousMultiplication J s n x : grading J (n + d)) : CoordinateRing J) =
      coordinateCoefficientMap f J C hJC (x : CoordinateRing J) *
        coordinateCoefficientMap f J C hJC (s : CoordinateRing J) := by
  exact map_mul _ _ _

/-- A regular equation on a coefficient-changed fibre multiplies
injectively on each homogeneous piece of that fibre. -/
theorem homogeneousMultiplication_coefficientFiber_injective_of_isRegular
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hJC : J.toIdeal.map (MvPolynomial.map f) = C.toIdeal)
    {d : ℕ} (s : grading J d)
    (hreg : IsRegular
      (coordinateCoefficientMap f J C hJC (s : CoordinateRing J)))
    (n : ℕ) :
    Function.Injective
      (homogeneousMultiplication C
        ⟨coordinateCoefficientMap f J C hJC (s : CoordinateRing J),
          coordinateCoefficientMap_mem f J C hJC s.2⟩ n) :=
  homogeneousMultiplication_injective_of_isRegular C _ hreg n

/-- On a local parameter chart, injectivity of one graded multiplication
map in the residue-field fibre implies injectivity of that map after
reduction by every coefficient ideal. -/
theorem homogeneousMultiplication_quotient_injective_of_residueField_injective
    {R : Type u} [CommRing R] [IsLocalRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    {d : ℕ} (s : grading J d) (n : ℕ)
    (hres : Function.Injective
      ((homogeneousMultiplication J s n).lTensor (ResidueField R)))
    (I : Ideal R) :
    Function.Injective
      ((homogeneousMultiplication J s n).lTensor (R ⧸ I)) := by
  letI : Module.Finite R (grading J n) :=
    coordinateRing_homogeneousPiece_finite J n
  letI : Module.Finite R (grading J (n + d)) :=
    coordinateRing_homogeneousPiece_finite J (n + d)
  letI : Module.Free R (grading J (n + d)) :=
    coordinateRing_homogeneousPiece_free_of_local J (n + d)
  exact lTensor_quotient_injective_of_residueField_injective
    (homogeneousMultiplication J s n) hres I

/-- Under the same fibre condition, the quotient of the degree-`n+d`
piece by the image of multiplication is flat over the local parameter
ring. This is the individual graded piece of the divisor family. -/
theorem homogeneousMultiplication_cokernel_flat_of_residueField_injective
    {R : Type u} [CommRing R] [IsLocalRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    {d : ℕ} (s : grading J d) (n : ℕ)
    (hres : Function.Injective
      ((homogeneousMultiplication J s n).lTensor (ResidueField R))) :
    Module.Flat R
      ((grading J (n + d)) ⧸ LinearMap.range (homogeneousMultiplication J s n)) := by
  letI : Module.Finite R (grading J n) :=
    coordinateRing_homogeneousPiece_finite J n
  letI : Module.Finite R (grading J (n + d)) :=
    coordinateRing_homogeneousPiece_finite J (n + d)
  letI : Module.Free R (grading J (n + d)) :=
    coordinateRing_homogeneousPiece_free_of_local J (n + d)
  exact cokernel_flat_of_residueField_injective
    (homogeneousMultiplication J s n) hres

end PfaffianDescent
