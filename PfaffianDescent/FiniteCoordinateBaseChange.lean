import PfaffianDescent.FiniteProjectiveCoordinates

/-!
# Finite coordinate data after scalar extension

This file records the algebraic part of base-changing projective coordinate
data.  If coordinates generate a finite algebra over the ground field, their
images generate the tensor-extended algebra.  Evaluation of a polynomial
after extending its coefficients agrees with the image of its original
evaluation.
-/

namespace PfaffianDescent

open MvPolynomial
open scoped TensorProduct

universe u

section

variable {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
  [Field L] [Algebra K L] {σ : Type*}

/-- Evaluating a coefficient-extended polynomial at the tensor images of the
original coordinates is the tensor image of the original evaluation. -/
theorem map_eval₂_tensorCoordinates
    (x : σ → A) (p : MvPolynomial σ K) :
    (p.map (algebraMap K L)).eval₂
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (fun k => Algebra.TensorProduct.includeRight (x k)) =
      Algebra.TensorProduct.includeRight
        (p.eval₂ (algebraMap K A) x) := by
  rw [MvPolynomial.eval₂_map,
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
  symm
  exact MvPolynomial.hom_eval₂ p (algebraMap K A)
    (Algebra.TensorProduct.includeRight
      (R := K) (A := L) (B := A)).toRingHom x

/-- A polynomial vanishing on the original coordinate datum continues to
vanish after scalar extension. -/
theorem map_eval₂_tensorCoordinates_eq_zero
    (x : σ → A) (p : MvPolynomial σ K)
    (hp : p.eval₂ (algebraMap K A) x = 0) :
    (p.map (algebraMap K L)).eval₂
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (fun k => Algebra.TensorProduct.includeRight (x k)) = 0 := by
  rw [map_eval₂_tensorCoordinates x p, hp, map_zero]

/-- A normalized polynomial remains normalized after scalar extension. -/
theorem map_eval₂_tensorCoordinates_eq_one
    (x : σ → A) (p : MvPolynomial σ K)
    (hp : p.eval₂ (algebraMap K A) x = 1) :
    (p.map (algebraMap K L)).eval₂
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (fun k => Algebra.TensorProduct.includeRight (x k)) = 1 := by
  rw [map_eval₂_tensorCoordinates x p, hp, map_one]

/-- Coordinates generating an algebra continue to generate the tensor
scalar extension. -/
theorem eval₂Hom_tensorCoordinates_surjective
    (x : σ → A)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x)) :
    Function.Surjective
      (eval₂Hom
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (fun k => Algebra.TensorProduct.includeRight (x k))) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      exact ⟨0, map_zero _⟩
  | add z w hz hw =>
      obtain ⟨p, hp⟩ := hz
      obtain ⟨q, hq⟩ := hw
      exact ⟨p + q, by rw [map_add, hp, hq]⟩
  | tmul l a =>
      obtain ⟨p, hp⟩ := hgen a
      refine ⟨C l * p.map (algebraMap K L), ?_⟩
      rw [map_mul, eval₂Hom_C, eval₂Hom_map_hom]
      have hcompat :
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A).comp
              (algebraMap K L) =
            (Algebra.TensorProduct.includeRight
              (R := K) (A := L) (B := A)).toRingHom.comp
              (algebraMap K A) := by
        ext k
        exact (Algebra.TensorProduct.includeLeft.commutes k).trans
          (Algebra.TensorProduct.includeRight.commutes k).symm
      rw [hcompat]
      let incR : A →+* L ⊗[K] A :=
        (Algebra.TensorProduct.includeRight
          (R := K) (A := L) (B := A)).toRingHom
      have heval :
          eval₂ (incR.comp (algebraMap K A)) (fun k => incR (x k)) p =
            incR ((eval₂Hom (algebraMap K A) x) p) := by
        symm
        exact MvPolynomial.map_eval₂Hom (algebraMap K A) x incR p
      change (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) l *
          eval₂ (incR.comp (algebraMap K A)) (fun k => incR (x k)) p = _
      rw [heval, hp]
      change (l ⊗ₜ[K] (1 : A)) * ((1 : L) ⊗ₜ[K] a) = l ⊗ₜ[K] a
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end

end PfaffianDescent
