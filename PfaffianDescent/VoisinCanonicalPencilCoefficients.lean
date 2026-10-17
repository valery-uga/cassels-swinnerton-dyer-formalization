import PfaffianDescent.VoisinQuadraticPencilScalarExtension
import PfaffianDescent.HomogeneousCoordinatesOverRing
import PfaffianDescent.VoisinIntrinsicQuadraticKernelIdeal
import PfaffianDescent.VoisinSectionLinearAlgebra

/-!
# Coefficients of the canonical unordered quadratic pencil

The canonical kernel basis over the unordered configuration field gives two
independent vectors in the ten-dimensional space of quadratic monomial
coefficients. This is the input needed to compare it with the ordered
eight-point matrix kernel.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.UniversalHomogeneous
open AllCharacteristics.HomogeneousProjective

universe u

noncomputable def quadraticHomogeneousCoefficients
    (K : Type u) [Field K] :
    homogeneousSubmodule (Fin 4) K 2 →ₗ[K]
      (Monomials (Fin 4) 2 → K) where
  toFun q m := q.1.coeff m.1
  map_add' q r := by
    ext m
    simp
  map_smul' a q := by
    ext m
    simp [smul_eq_C_mul]

theorem quadraticHomogeneousCoefficients_injective
    (K : Type u) [Field K] :
    Function.Injective (quadraticHomogeneousCoefficients K) := by
  classical
  let e : Fin 10 ≃ Monomials (Fin 4) 2 :=
    (Fintype.equivFinOfCardEq (by
      simpa using quadraticMonomials_card)).symm
  let E := homogeneousCoefficientLinearEquivOverRing
    (R := K) (σ := Fin 4) 2 e
  intro q r h
  apply E.injective
  apply _root_.funext
  intro i
  exact congrFun h (e i)

/-- Coefficient extraction preserves independence of homogeneous quadrics. -/
theorem quadraticHomogeneousCoefficients_linearIndependent
    (K : Type u) [Field K] {ι : Type*}
    (v : ι → homogeneousSubmodule (Fin 4) K 2)
    (hv : LinearIndependent K v) :
    LinearIndependent K (quadraticHomogeneousCoefficients K ∘ v) :=
  hv.map' (quadraticHomogeneousCoefficients K)
    (LinearMap.ker_eq_bot.mpr (quadraticHomogeneousCoefficients_injective K))

/-- Every rank-eight coordinate algebra has two independent homogeneous
quadrics vanishing in it, directly in the ambient quadric space. -/
theorem exists_rankEight_independentVanishingHomogeneousQuadrics
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8) :
    ∃ q : Fin 2 → homogeneousSubmodule (Fin 4) K 2,
      LinearIndependent K q ∧
      ∀ i, (q i).1.eval₂ (algebraMap K A) x = 0 := by
  have hdim : Module.finrank K A + 1 <
      Module.finrank K (homogeneousSubmodule (Fin 4) K 2) := by
    rw [hA, four_variable_homogeneous_finrank]
    decide
  obtain ⟨q, hq, hzero⟩ :=
    exists_linearIndependent_pair_mem_ker_of_finrank_target_lt
      (homogeneousSectionRestriction (K := K) x 2) hdim
  refine ⟨q, hq, ?_⟩
  intro i
  simpa only [homogeneousSectionRestriction_apply] using hzero i

/-- The degree-two coefficient vector reconstructs the original homogeneous
quadric, so its finite-algebra and ordered-point evaluations agree. -/
theorem quadraticPolynomialOfHomogeneousCoefficients
    (K : Type u) [Field K]
    (q : homogeneousSubmodule (Fin 4) K 2) :
    quadraticPolynomialOfCoefficients
      (quadraticHomogeneousCoefficients K q) = q.1 := by
  classical
  let e : Fin 10 ≃ Monomials (Fin 4) 2 :=
    (Fintype.equivFinOfCardEq (by
      simpa using quadraticMonomials_card)).symm
  let E := homogeneousCoefficientLinearEquivOverRing
    (R := K) (σ := Fin 4) 2 e
  have h : (⟨quadraticPolynomialOfCoefficients
        (quadraticHomogeneousCoefficients K q),
      quadraticPolynomialOfCoefficients_isHomogeneous _⟩ :
        homogeneousSubmodule (Fin 4) K 2) = q := by
    apply E.injective
    funext i
    exact coeff_quadraticPolynomialOfCoefficients _ (e i)
  exact congrArg Subtype.val h

/-- A homogeneous quadric that vanishes in the finite coordinate algebra
gives an element of the ordered eight-point evaluation kernel whenever the
component maps jointly detect that algebra. -/
theorem quadraticHomogeneousCoefficients_mem_splitKernel
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : homogeneousSubmodule (Fin 4) K 2)
    (hzero : q.1.eval₂ (algebraMap K A) x = 0) :
    (fun m => algebraMap K L (quadraticHomogeneousCoefficients K q m)) ∈
      LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix
          (fun i j => φ i (x j)))) := by
  apply (quadraticCoefficients_vanish_iff_splitMatrixKernel
    φ hφ x (quadraticHomogeneousCoefficients K q)).mp
  rw [quadraticPolynomialOfHomogeneousCoefficients]
  exact hzero

/-- Two independent homogeneous quadrics vanishing in a jointly detected
finite algebra become a basis of the complete ordered eight-point kernel on
a selected minor chart. -/
theorem quadraticHomogeneousPair_span_splitKernel
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2)
    (hq : LinearIndependent K q)
    (hzero : ∀ i, (q i).1.eval₂ (algebraMap K A) x = 0)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det) :
    Submodule.span L (Set.range (fun i : Fin 2 =>
      fun a => algebraMap K L (quadraticHomogeneousCoefficients K (q i) a))) =
      LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix
          (fun i j => φ i (x j)))) := by
  exact quadraticCoefficientPair_span_orderedKernel
    (fun i => quadraticHomogeneousCoefficients K (q i))
    (quadraticHomogeneousCoefficients_linearIndependent K q hq)
    (fun i j => φ i (x j)) m hminor
    (fun i => quadraticHomogeneousCoefficients_mem_splitKernel
      φ hφ x (q i) (hzero i))

/-- The two unordered homogeneous quadrics generate the intrinsic quadratic
ideal of the ordered points after extension to a selected minor chart. -/
theorem quadraticHomogeneousPair_intrinsicIdeal
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2)
    (hq : LinearIndependent K q)
    (hzero : ∀ i, (q i).1.eval₂ (algebraMap K A) x = 0)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det) :
    intrinsicEightPointQuadraticIdeal (fun i j => φ i (x j)) =
      Ideal.span (Set.range (fun i : Fin 2 =>
        quadraticPolynomialOfCoefficients
          (fun a => algebraMap K L
            (quadraticHomogeneousCoefficients K (q i) a)))) := by
  let v : Fin 2 → Monomials (Fin 4) 2 → L :=
    fun i a => algebraMap K L (quadraticHomogeneousCoefficients K (q i) a)
  have hmem : ∀ i, v i ∈ LinearMap.ker
      (Matrix.toLin' (eightPointQuadraticEvaluationMatrix
        (fun i j => φ i (x j)))) := by
    intro i
    exact quadraticHomogeneousCoefficients_mem_splitKernel
      φ hφ x (q i) (hzero i)
  have hspan : Submodule.span L (Set.range v) =
      LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix
          (fun i j => φ i (x j)))) :=
    quadraticHomogeneousPair_span_splitKernel
      φ hφ x q hq hzero m hminor
  exact intrinsicEightPointQuadraticIdeal_eq_pair_of_span
    (fun i j => φ i (x j)) v hmem hspan

/-- The intrinsic ordered ideal is generated by the literal coefficient
extensions of the two ground-field homogeneous quadrics. -/
theorem quadraticHomogeneousPair_intrinsicIdeal_eq_mappedPolynomials
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2)
    (hq : LinearIndependent K q)
    (hzero : ∀ i, (q i).1.eval₂ (algebraMap K A) x = 0)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det) :
    intrinsicEightPointQuadraticIdeal (fun i j => φ i (x j)) =
      Ideal.span (Set.range (fun i : Fin 2 =>
        (q i).1.map (algebraMap K L))) := by
  have h := quadraticHomogeneousPair_intrinsicIdeal
    φ hφ x q hq hzero m hminor
  have heq : (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients
        (fun a => algebraMap K L
          (quadraticHomogeneousCoefficients K (q i) a))) =
      (fun i : Fin 2 => (q i).1.map (algebraMap K L)) := by
    funext i
    rw [← quadraticPolynomialOfCoefficients_map,
      quadraticPolynomialOfHomogeneousCoefficients]
  rw [heq] at h
  exact h

/-- Adding the cubic equation gives equality of the literal triple
intersection ideal over the ordered splitting field. -/
theorem quadraticHomogeneousPair_intrinsicTripleIdeal_eq_mappedPolynomials
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2)
    (hq : LinearIndependent K q)
    (hzero : ∀ i, (q i).1.eval₂ (algebraMap K A) x = 0)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det)
    (p : MvPolynomial (Fin 4) K) :
    intrinsicEightPointTripleIdeal
      (p.map (algebraMap K L)) (fun i j => φ i (x j)) =
      Ideal.span (insert (p.map (algebraMap K L))
        (Set.range (fun i : Fin 2 =>
          (q i).1.map (algebraMap K L)))) := by
  rw [intrinsicEightPointTripleIdeal,
    quadraticHomogeneousPair_intrinsicIdeal_eq_mappedPolynomials
      φ hφ x q hq hzero m hminor,
    Ideal.span_insert]

end PfaffianDescent
