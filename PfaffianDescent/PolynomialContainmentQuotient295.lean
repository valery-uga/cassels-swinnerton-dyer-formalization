import PfaffianDescent.PolynomialContainmentChart291
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Actual coefficient quotients for polynomial containment. The equations are
those of the original cyclic point, with no assumed representative. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry
universe u
variable (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]

/-- Quotient algebra maps classify precisely the original maps killing the ideal. -/
def quotientAlgHomKernelEquiv295 (I : Ideal C)
    (A : Type u) [CommRing A] [Algebra R A] :
    (C ⧸ I →ₐ[R] A) ≃ {f : C →ₐ[R] A // I ≤ RingHom.ker f.toRingHom} where
  toFun g := ⟨g.comp (Ideal.Quotient.mkₐ R I), by
    intro x hx
    change g (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩
  invFun f := Ideal.Quotient.liftₐ I f.val (fun x hx => f.property hx)
  left_inv g := by
    apply Ideal.Quotient.algHom_ext
    exact Ideal.Quotient.liftₐ_comp I _ _
  right_inv f := by
    apply Subtype.ext
    exact Ideal.Quotient.liftₐ_comp I _ _

lemma quotientAlgHomKernelEquiv_restrict295 (I : Ideal C)
    {A : Type u} [CommRing A] [Algebra R A] (g : C ⧸ I →ₐ[R] A) :
    (quotientAlgHomKernelEquiv295 R C I A g).val =
      g.comp (Ideal.Quotient.mkₐ R I) := rfl

lemma quotientAlgHomKernelEquiv_natural295 (I : Ideal C)
    {A D : Type u} [CommRing A] [CommRing D] [Algebra R A] [Algebra R D]
    (g : C ⧸ I →ₐ[R] A) (f : A →ₐ[R] D) :
    (quotientAlgHomKernelEquiv295 R C I D (f.comp g)).val =
      f.comp (quotientAlgHomKernelEquiv295 R C I A g).val := rfl

variable {m n : ℕ} (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
variable (M : CyclicCommutingMatrixPoint283 m n B k (A := C))
variable (p : MvPolynomial (Fin m) C)

/-- The actual quotient of the original coefficient algebra by the finite equations. -/
abbrev PolynomialContainmentCoefficientAlgebra295 :=
  C ⧸ cyclicPolynomialContainmentIdeal291 B k M p

/-- Maps out of this quotient classify exactly containment after specialization. -/
def polynomialContainmentQuotientAlgHomEquiv295
    (A : Type u) [CommRing A] [Algebra R A] :
    (PolynomialContainmentCoefficientAlgebra295 C B k M p →ₐ[R] A) ≃
      {f : C →ₐ[R] A // MvPolynomial.map f.toRingHom p ∈
        (cyclicMatrixWholeIdealChart287 B k
          (cyclicMatrixPointMap287 B k f.toRingHom M)).val} :=
  (quotientAlgHomKernelEquiv295 R C
    (cyclicPolynomialContainmentIdeal291 B k M p) A).trans
      (Equiv.subtypeEquivRight (fun f =>
        cyclicPolynomialContainmentIdeal_le_ker_iff291 B k M f.toRingHom p))

lemma polynomialContainmentQuotientAlgHomEquiv_restrict295
    {A : Type u} [CommRing A] [Algebra R A]
    (g : PolynomialContainmentCoefficientAlgebra295 C B k M p →ₐ[R] A) :
    (polynomialContainmentQuotientAlgHomEquiv295 R C B k M p A g).val =
      g.comp (Ideal.Quotient.mkₐ R (cyclicPolynomialContainmentIdeal291 B k M p)) := rfl

lemma polynomialContainmentQuotientAlgHomEquiv_natural295
    {A D : Type u} [CommRing A] [CommRing D] [Algebra R A] [Algebra R D]
    (g : PolynomialContainmentCoefficientAlgebra295 C B k M p →ₐ[R] A)
    (f : A →ₐ[R] D) :
    (polynomialContainmentQuotientAlgHomEquiv295 R C B k M p D (f.comp g)).val =
      f.comp (polynomialContainmentQuotientAlgHomEquiv295 R C B k M p A g).val := rfl

/-- The constructed hypersurface condition is a native closed immersion of coefficient schemes. -/
lemma polynomialContainmentCoefficient_isClosedImmersion295 :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (cyclicPolynomialContainmentIdeal291 B k M p)))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

end PfaffianDescent
