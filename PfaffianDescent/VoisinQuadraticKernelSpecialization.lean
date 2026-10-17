import PfaffianDescent.VoisinQuadraticSelectedOpenFrame
import PfaffianDescent.VoisinEightNormalizedEvaluation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Specializing a quadratic evaluation-kernel vector

Coefficientwise base change carries a quadratic vanishing at eight points
to a quadratic vanishing at their specialized images. This is the first
step toward comparing the local open-chart frame with the split fiber.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u v

def mapEightPointQuadraticEvaluationKernel
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S]
    (f : R →+* S)
    (y : Fin 8 → Fin 4 → R)
    (q : LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))) :
    LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix
      (fun k j => f (y k j)))) := by
  refine ⟨fun a => f (q.1 a), ?_⟩
  apply _root_.funext
  intro k
  have hk := congrFun q.2 k
  have hmap := congrArg f hk
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Pi.zero_apply, map_zero, map_sum, map_mul] at hmap
  simpa only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Pi.zero_apply, ← eightPointQuadraticEvaluationMatrix_map,
    Matrix.map_apply] using hmap

theorem quadraticPolynomialOfCoefficients_map
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S]
    (f : R →+* S) (q : Monomials (Fin 4) 2 → R) :
    (quadraticPolynomialOfCoefficients q).map f =
      quadraticPolynomialOfCoefficients (fun a => f (q a)) := by
  classical
  simp [quadraticPolynomialOfCoefficients]

noncomputable def quadraticSelectedOpenBasisSpecializedVector
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (i : Fin 2) :
    LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix
      (fun k j => f (y k j)))) := by
  let S := Localization.Away (quadraticMinorDet m y)
  let g := quadraticMinorSelectedPointLift m y f h
  let yS : Fin 8 → Fin 4 → S :=
    fun k j => algebraMap R S (y k j)
  have hy : (fun k j => g (yS k j)) =
      (fun k j => f (y k j)) := by
    funext k j
    have hg := quadraticMinorSelectedPointLift_comp m y f h
    exact congrArg (fun φ : R →+* F => φ (y k j)) hg
  have hq := mapEightPointQuadraticEvaluationKernel g yS
    (quadraticSelectedOpenFullKernelBasis m y i)
  refine ⟨hq.1, ?_⟩
  simpa only [hy] using hq.2

/-- Specializing the regular equation on the determinant open gives the
homogeneous quadratic built from the specialized kernel vector. -/
theorem quadraticSelectedOpenPolynomial_map_selectedPoint
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (i : Fin 2) :
    (quadraticSelectedOpenPolynomial m y i).map
      (quadraticMinorSelectedPointLift m y f h) =
      quadraticPolynomialOfCoefficients
        (quadraticSelectedOpenBasisSpecializedVector m y f h i).1 := by
  rw [quadraticSelectedOpenPolynomial,
    quadraticPolynomialOfCoefficients_map]
  rfl

theorem quadraticSelectedOpenBasisSpecializedVector_polynomial_data
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (i : Fin 2) :
    (quadraticPolynomialOfCoefficients
      (quadraticSelectedOpenBasisSpecializedVector m y f h i).1).IsHomogeneous 2 ∧
    ∀ k : Fin 8,
      (quadraticPolynomialOfCoefficients
        (quadraticSelectedOpenBasisSpecializedVector m y f h i).1).eval
          (fun j => f (y k j)) = 0 := by
  exact ⟨quadraticPolynomialOfCoefficients_isHomogeneous _,
    fun k => quadraticPolynomialOfCoefficients_eval_zero_of_mem_ker
      (fun k j => f (y k j))
      (quadraticSelectedOpenBasisSpecializedVector m y f h i) k⟩

theorem quadraticSelectedOpenBasisSpecializedVector_complement
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (i j : Fin 2) :
    (quadraticSelectedOpenBasisSpecializedVector m y f h i).1
      (quadraticMonomialPartition m (Sum.inr j)) =
        (Pi.basisFun F (Fin 2) i) j := by
  let g := quadraticMinorSelectedPointLift m y f h
  have hl := quadraticSelectedOpenFullKernelBasis_complement m y i j
  have hmap := congrArg g hl
  simpa [quadraticSelectedOpenBasisSpecializedVector,
    mapEightPointQuadraticEvaluationKernel, Pi.basisFun_apply,
    Pi.single_apply] using hmap

/-- The two specialized local-frame vectors are linearly independent:
their complementary monomial coefficients are the standard basis. -/
theorem quadraticSelectedOpenBasisSpecializedVector_linearIndependent
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    LinearIndependent F
      (quadraticSelectedOpenBasisSpecializedVector m y f h) := by
  let M := eightPointQuadraticEvaluationMatrix
    (fun k j => f (y k j))
  let T : LinearMap.ker (Matrix.toLin' M) →ₗ[F] (Fin 2 → F) :=
    (LinearMap.funLeft F F
      (fun j => quadraticMonomialPartition m (Sum.inr j))).comp
      (LinearMap.ker (Matrix.toLin' M)).subtype
  apply LinearIndependent.of_comp T
  have heq : (T ∘ quadraticSelectedOpenBasisSpecializedVector m y f h) =
      Pi.basisFun F (Fin 2) := by
    funext i j
    exact quadraticSelectedOpenBasisSpecializedVector_complement m y f h i j
  rw [heq]
  exact (Pi.basisFun F (Fin 2)).linearIndependent

/-- The specialized regular frame is a basis of the full selected-fiber
quadratic kernel, because that kernel has dimension two. -/
noncomputable def quadraticSelectedOpenBasisSpecializedBasis
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    Module.Basis (Fin 2) F
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix
          (fun k j => f (y k j))))) := by
  have hdim := eightPointQuadraticEvaluationMatrix_kernel_finrank_two
    (fun k j => f (y k j)) m h
  exact basisOfLinearIndependentOfCardEqFinrank
    (quadraticSelectedOpenBasisSpecializedVector_linearIndependent m y f h)
    (by simpa using hdim.symm)

@[simp] theorem quadraticSelectedOpenBasisSpecializedBasis_apply
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (i : Fin 2) :
    quadraticSelectedOpenBasisSpecializedBasis m y f h i =
      quadraticSelectedOpenBasisSpecializedVector m y f h i := by
  simp [quadraticSelectedOpenBasisSpecializedBasis]

theorem quadraticSelectedOpenBasisSpecialized_polynomial_linearIndependent
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    LinearIndependent F
      (fun i : Fin 2 => quadraticPolynomialOfCoefficients
        (quadraticSelectedOpenBasisSpecializedVector m y f h i).1) := by
  let M := eightPointQuadraticEvaluationMatrix
    (fun k j => f (y k j))
  let T : LinearMap.ker (Matrix.toLin' M) →ₗ[F]
      MvPolynomial (Fin 4) F :=
    (quadraticPolynomialOfCoefficientsLinearMap F).comp
      (LinearMap.ker (Matrix.toLin' M)).subtype
  have hT : Function.Injective T :=
    (quadraticPolynomialOfCoefficientsLinearMap_injective F).comp
      Subtype.val_injective
  have hli :=
    (quadraticSelectedOpenBasisSpecializedBasis m y f h).linearIndependent.map'
      T (LinearMap.ker_eq_bot.mpr hT)
  have heq : (T ∘ ⇑(quadraticSelectedOpenBasisSpecializedBasis m y f h)) =
      (fun i : Fin 2 => quadraticPolynomialOfCoefficients
        (quadraticSelectedOpenBasisSpecializedVector m y f h i).1) := by
    funext i
    change (quadraticPolynomialOfCoefficientsLinearMap F)
      (quadraticSelectedOpenBasisSpecializedBasis m y f h i).1 = _
    rw [quadraticSelectedOpenBasisSpecializedBasis_apply]
    rfl
  rw [heq] at hli
  exact hli

theorem homogeneousQuadric_mem_eightPointRestrictionKernel_of_eval_zero
    {F : Type v} [Field F]
    (p : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 2)
    (y : Fin 8 → Fin 4 → F)
    (hzero : ∀ k, p.eval (y k) = 0) :
    (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) F 2) ∈
      LinearMap.ker (homogeneousSectionRestriction (K := F)
        (fun j k => y k j : Fin 4 → Fin 8 → F) 2) := by
  rw [LinearMap.mem_ker]
  change p.eval₂ (algebraMap F (Fin 8 → F))
    (fun j k => y k j) = 0
  apply _root_.funext
  intro k
  have heval := polynomial_eval_algEquiv_pi_apply
    (AlgEquiv.refl : (Fin 8 → F) ≃ₐ[F] (Fin 8 → F))
    (fun j k => y k j) p k
  simpa using (heval.trans (hzero k))

noncomputable def quadraticSelectedOpenBasisSpecializedHomogeneous
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (i : Fin 2) : homogeneousSubmodule (Fin 4) F 2 :=
  ⟨quadraticPolynomialOfCoefficients
      (quadraticSelectedOpenBasisSpecializedVector m y f h i).1,
    (quadraticSelectedOpenBasisSpecializedVector_polynomial_data
      m y f h i).1⟩

theorem quadraticSelectedOpenBasisSpecializedHomogeneous_mem_kernel
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (i : Fin 2) :
    quadraticSelectedOpenBasisSpecializedHomogeneous m y f h i ∈
      LinearMap.ker (homogeneousSectionRestriction (K := F)
        (fun j k => f (y k j) : Fin 4 → Fin 8 → F) 2) := by
  exact homogeneousQuadric_mem_eightPointRestrictionKernel_of_eval_zero
    _ (quadraticSelectedOpenBasisSpecializedVector_polynomial_data
        m y f h i).1
    (fun k j => f (y k j))
    (quadraticSelectedOpenBasisSpecializedVector_polynomial_data
      m y f h i).2

theorem quadraticSelectedOpenBasisSpecializedHomogeneous_linearIndependent
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det) :
    LinearIndependent F
      (quadraticSelectedOpenBasisSpecializedHomogeneous m y f h) := by
  apply LinearIndependent.of_comp
    (homogeneousSubmodule (Fin 4) F 2).subtype
  exact quadraticSelectedOpenBasisSpecialized_polynomial_linearIndependent
    m y f h

theorem span_eq_kernel_of_two_independent_members
    {F : Type v} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W]
    (T : V →ₗ[F] W) (q : Fin 2 → V)
    (hmem : ∀ i, q i ∈ LinearMap.ker T)
    (hli : LinearIndependent F q)
    (hdim : Module.finrank F (LinearMap.ker T) = 2) :
    Submodule.span F (Set.range q) = LinearMap.ker T := by
  let H := LinearMap.ker T
  have hliH : LinearIndependent F (fun i : Fin 2 => (⟨q i, hmem i⟩ : H)) := by
    apply LinearIndependent.of_comp H.subtype
    exact hli
  have hcard : Fintype.card (Fin 2) = Module.finrank F H := by
    change Fintype.card (Fin 2) = Module.finrank F (LinearMap.ker T)
    rw [hdim]
    decide
  have hspan : Submodule.span F
      (Set.range (fun i : Fin 2 => (⟨q i, hmem i⟩ : H))) = ⊤ :=
    hliH.span_eq_top_of_card_eq_finrank hcard
  exact (Submodule.span_range_subtype_eq_top_iff H hmem).mp hspan

/-- If the selected quadratic restriction is surjective, the two
specialized local equations span its full homogeneous kernel. -/
theorem quadraticSelectedOpenBasisSpecializedHomogeneous_span_eq_kernel
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (f : R →+* F)
    (h : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := F)
        (fun j k => f (y k j) : Fin 4 → Fin 8 → F) 2)) :
    Submodule.span F
      (Set.range (quadraticSelectedOpenBasisSpecializedHomogeneous m y f h)) =
    LinearMap.ker (homogeneousSectionRestriction (K := F)
      (fun j k => f (y k j) : Fin 4 → Fin 8 → F) 2) := by
  have hdim : Module.finrank F (LinearMap.ker
      (homogeneousSectionRestriction (K := F)
        (fun j k => f (y k j) : Fin 4 → Fin 8 → F) 2)) = 2 :=
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      (fun j k => f (y k j)) (by simp) hsurj
  exact span_eq_kernel_of_two_independent_members
    (homogeneousSectionRestriction (K := F)
      (fun j k => f (y k j) : Fin 4 → Fin 8 → F) 2)
    (quadraticSelectedOpenBasisSpecializedHomogeneous m y f h)
    (quadraticSelectedOpenBasisSpecializedHomogeneous_mem_kernel m y f h)
    (quadraticSelectedOpenBasisSpecializedHomogeneous_linearIndependent m y f h)
    hdim

end PfaffianDescent
