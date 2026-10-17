import PfaffianDescent.VoisinSelectedSplitPencilComparison
import PfaffianDescent.VoisinIntrinsicQuadraticKernelIdeal
import PfaffianDescent.VoisinFiniteAlgebraPencilProjectiveOverBase

/-!
# Descending a finite selected quadratic pair

A finite geometric cubic--two-quadric intersection at an extension-field
specialization makes the canonical selected pair finite over the smaller
field.  This is the algebraic core of the remaining residue-point descent.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem selectedQuadraticPair_isFinite_of_extension_specialization
    {Q L : Type u} [Field Q] [Field L] [Algebra Q L]
    (x : Fin 8 → Fin 4 → Q)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hmQ : IsUnit (eightPointQuadraticEvaluationMinor m x).det)
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (hxy : ∀ k j, algebraMap Q L (x k j) =
      normalizedVectorInLinearChart c (y k) j)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k, q.eval (y k) = 0 ∧ r.eval (y k) = 0)
    (p : MvPolynomial (Fin 4) Q) (hp : p.IsHomogeneous 3)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap Q L)) q r (hp.map (algebraMap Q L)) hq hr))] :
    let hid : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => (RingHom.id Q) (x k j))).det := by simpa using hmQ
    let b := quadraticSelectedOpenBasisSpecializedBasis m x (RingHom.id Q) hid
    IsFinite (relativeTripleIntersectionToBase p
      (quadraticPolynomialOfCoefficients (b 0).1)
      (quadraticPolynomialOfCoefficients (b 1).1) hp
      (quadraticPolynomialOfCoefficients_isHomogeneous (b 0).1)
      (quadraticPolynomialOfCoefficients_isHomogeneous (b 1).1)) := by
  dsimp only
  let hid : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => (RingHom.id Q) (x k j))).det := by
    simpa using hmQ
  let b := quadraticSelectedOpenBasisSpecializedBasis m x (RingHom.id Q) hid
  let qQ : Fin 2 → homogeneousSubmodule (Fin 4) Q 2 :=
    quadraticSelectedOpenBasisSpecializedHomogeneous m x (RingHom.id Q) hid
  have hqQ : LinearIndependent Q qQ := by
    exact quadraticSelectedOpenBasisSpecializedHomogeneous_linearIndependent
      m x (RingHom.id Q) hid
  let A := Fin 8 → Q
  let xA : Fin 4 → A := fun j k => x k j
  let φ : Fin 8 → A →ₐ[Q] L := fun i =>
    (Algebra.ofId Q L).comp (Pi.evalAlgHom Q (fun _ : Fin 8 => Q) i)
  have hφ : Function.Injective (fun t : A => fun i => φ i t) := by
    intro a b hab
    funext i
    apply (algebraMap Q L).injective
    exact congrFun hab i
  have hzero : ∀ i, (qQ i).1.eval₂ (algebraMap Q A) xA = 0 := by
    intro i
    have hi := quadraticSelectedOpenBasisSpecializedHomogeneous_mem_kernel
      m x (RingHom.id Q) hid i
    rw [LinearMap.mem_ker] at hi
    change homogeneousSectionRestriction (K := Q)
      (fun j k => x k j : Fin 4 → Fin 8 → Q) 2 (qQ i) = 0
    simpa only [qQ, RingHom.id_apply] using hi
  have hmL : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => algebraMap Q L (x k j))).det := by
    rw [← eightPointQuadraticEvaluationMinor_map]
    change IsUnit ((algebraMap Q L).mapMatrix
      (eightPointQuadraticEvaluationMinor m x)).det
    rw [← RingHom.map_det]
    exact hmQ.map (algebraMap Q L)
  let bL := quadraticSelectedOpenBasisSpecializedBasis
    m x (algebraMap Q L) hmL
  let I := intrinsicEightPointTripleHomogeneousIdeal
    (p.map (algebraMap Q L)) (hp.map (algebraMap Q L))
    (fun k j => algebraMap Q L (x k j))
  have hIselected : I = relativeTripleIntersectionHomogeneousIdeal
      (p.map (algebraMap Q L))
      (quadraticPolynomialOfCoefficients (bL 0).1)
      (quadraticPolynomialOfCoefficients (bL 1).1)
      (hp.map (algebraMap Q L))
      (quadraticPolynomialOfCoefficients_isHomogeneous (bL 0).1)
      (quadraticPolynomialOfCoefficients_isHomogeneous (bL 1).1) :=
    intrinsicEightPointTripleHomogeneousIdeal_eq_relative_of_basis
      (p.map (algebraMap Q L)) (hp.map (algebraMap Q L))
      (fun k j => algebraMap Q L (x k j)) bL
  have hselectedPair : relativeTripleIntersectionHomogeneousIdeal
      (p.map (algebraMap Q L))
      (quadraticPolynomialOfCoefficients (bL 0).1)
      (quadraticPolynomialOfCoefficients (bL 1).1)
      (hp.map (algebraMap Q L))
      (quadraticPolynomialOfCoefficients_isHomogeneous (bL 0).1)
      (quadraticPolynomialOfCoefficients_isHomogeneous (bL 1).1) =
      tripleCompleteIntersectionHomogeneousIdeal
        (p.map (algebraMap Q L)) q r
        (hp.map (algebraMap Q L)) hq hr := by
    change tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap Q L))
      (quadraticPolynomialOfCoefficients (bL 0).1)
      (quadraticPolynomialOfCoefficients (bL 1).1)
      (hp.map (algebraMap Q L))
      (quadraticPolynomialOfCoefficients_isHomogeneous (bL 0).1)
      (quadraticPolynomialOfCoefficients_isHomogeneous (bL 1).1) = _
    simpa only [bL, quadraticSelectedOpenBasisSpecializedBasis_apply,
      quadraticSelectedOpenBasisSpecializedHomogeneous] using
      (quadraticSelectedOpenBasisSpecialized_ideal_eq_quadratic_pair
        m x (algebraMap Q L) hmL y c hc hxy q r hq hr hlin hsurj hquad
        (p.map (algebraMap Q L)) (hp.map (algebraMap Q L)))
  have hIfin : IsFinite (toBase I) := by
    rw [hIselected, hselectedPair]
    infer_instance
  letI : IsFinite (toBase I) := hIfin
  have hmφ : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (xA j))).det := by
    change IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => algebraMap Q L (x i j))).det
    exact hmL
  let C := quadraticHomogeneousPair_intrinsicProjectiveComparisonOverBase
    φ hφ xA qQ hqQ hzero m hmφ p hp
  have hfinQ := C.isFinite_unordered p (qQ 0).1 (qQ 1).1 hp
    (qQ 0).2 (qQ 1).2 I
  have hqpoly (i : Fin 2) : (qQ i).1 =
      quadraticPolynomialOfCoefficients (b i).1 := by
    simp only [qQ, b, quadraticSelectedOpenBasisSpecializedHomogeneous,
      quadraticSelectedOpenBasisSpecializedBasis_apply]
  let qb : Fin 2 → homogeneousSubmodule (Fin 4) Q 2 := fun i =>
    ⟨quadraticPolynomialOfCoefficients (b i).1,
      quadraticPolynomialOfCoefficients_isHomogeneous (b i).1⟩
  have hqb : qQ = qb := by
    funext i
    exact Subtype.ext (hqpoly i)
  rw [hqb] at hfinQ
  simpa only [qb] using hfinQ

end PfaffianDescent
