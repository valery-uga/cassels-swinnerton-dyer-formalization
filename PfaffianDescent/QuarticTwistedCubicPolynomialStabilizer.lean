import PfaffianDescent.QuarticTwistedCubicPointParametrization

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u
variable {K : Type u} [Field K]

/-- Every cubic-Veronese point over an arbitrary commutative `K`-algebra
annihilates the standard twisted-cubic ideal. -/
theorem standardTwistedCubicIdeal_aeval_cubicVeronese
    {A : Type u} [CommRing A] [Algebra K A]
    (s t : A) (p : MvPolynomial (Fin 4) K)
    (hp : p ∈ standardTwistedCubicIdeal K) :
    MvPolynomial.aeval (cubicVeronese s t) p = 0 := by
  rw [standardTwistedCubicIdeal_eq_ker] at hp
  rw [← standardTwistedCubicParam_eval]
  change standardTwistedCubicParam K p = 0 at hp
  rw [hp, map_zero]

/-- The four cubic polynomials obtained by applying a standard-ideal-
preserving matrix to the affine cubic Veronese satisfy the three Hankel
relations identically. -/
theorem linearSubstitution_preserving_standardTwistedCubic_aeval_relations
    (B : Matrix (Fin 4) (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map (linearSubstitution B).toRingHom =
      standardTwistedCubicIdeal K)
    {A : Type u} [CommRing A] [Algebra K A] (s t : A) :
    (((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 1) ^ 2 =
        ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 0 *
          ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 2 ∧
      ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 1 *
          ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 2 =
        ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 0 *
          ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 3 ∧
      (((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 2) ^ 2 =
        ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 1 *
          ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) 3 := by
  have hpoint (p : MvPolynomial (Fin 4) K) (hp : p ∈ standardTwistedCubicIdeal K) :
      MvPolynomial.aeval ((B.map (algebraMap K A)).mulVec (cubicVeronese s t)) p = 0 := by
    rw [← linearSubstitution_aeval]
    apply standardTwistedCubicIdeal_aeval_cubicVeronese
    rw [← hB]
    exact Ideal.mem_map_of_mem _ hp
  have h0 := hpoint (standardTwistedCubicGenerators K 0)
    (Ideal.subset_span (Set.mem_range_self 0))
  have h1 := hpoint (standardTwistedCubicGenerators K 1)
    (Ideal.subset_span (Set.mem_range_self 1))
  have h2 := hpoint (standardTwistedCubicGenerators K 2)
    (Ideal.subset_span (Set.mem_range_self 2))
  constructor
  · exact sub_eq_zero.mp (by simpa [standardTwistedCubicGenerators] using h0)
  constructor
  · exact sub_eq_zero.mp (by simpa [standardTwistedCubicGenerators] using h1)
  · exact sub_eq_zero.mp (by simpa [standardTwistedCubicGenerators] using h2)

/-- The affine parameter-line specialization of the preceding polynomial
identities. -/
theorem linearSubstitution_preserving_standardTwistedCubic_polynomial_relations
    (B : Matrix (Fin 4) (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map (linearSubstitution B).toRingHom =
      standardTwistedCubicIdeal K) :
    let z : Fin 4 → Polynomial K :=
      (B.map (algebraMap K (Polynomial K))).mulVec
        (cubicVeronese (1 : Polynomial K) Polynomial.X)
    z 1 ^ 2 = z 0 * z 2 ∧ z 1 * z 2 = z 0 * z 3 ∧ z 2 ^ 2 = z 1 * z 3 := by
  exact linearSubstitution_preserving_standardTwistedCubic_aeval_relations B hB
    (1 : Polynomial K) Polynomial.X

end PfaffianDescent.QuarticNet
