import PfaffianDescent.CorayAlgClosedFiniteTypeTensorDomain
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.FiniteType

/-!
# Literal polynomial quotient transport and arbitrary-field prime extension

The native tensor quotient is transported through the native polynomial tensor
isomorphism. Its defining ideal is proved to be the WHOLE literal coefficient
extension, and its tensor-generator formula records the actual map. The
pending finite-type tensor-domain construction then yields primeness over ANY
extension field of an algebraically closed coefficient field.
SOURCE ONLY / UNVERIFIED: root owns compilation and auditing.
-/
noncomputable section
namespace PfaffianDescent.Coray
open scoped TensorProduct
universe u v
variable {Ω : Type u} {T : Type v} [Field Ω] [Field T] [Algebra Ω T]

/-- The actual quotient by the whole coefficient-extended ideal, obtained from
native tensor/quotient and polynomial/tensor algebra equivalences. -/
def polynomialCoefficientQuotientTensorEquiv (P : Ideal (MvPolynomial (Fin 4) Ω)) :
    T ⊗[Ω] (MvPolynomial (Fin 4) Ω ⧸ P) ≃ₐ[T]
      MvPolynomial (Fin 4) T ⧸ P.map (MvPolynomial.map (algebraMap Ω T)) := by
  let b := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) Ω T
  let ι : MvPolynomial (Fin 4) Ω →+* T ⊗[Ω] MvPolynomial (Fin 4) Ω :=
    (Algebra.TensorProduct.includeRight (R := Ω) (A := T)).toRingHom
  have hcomp : b.toRingHom.comp ι = MvPolynomial.map (algebraMap Ω T) := by
    apply RingHom.ext
    intro q
    change b (1 ⊗ₜ[Ω] q) = MvPolynomial.map (algebraMap Ω T) q
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  have hmap : (P.map ι).map b.toRingHom = P.map (MvPolynomial.map (algebraMap Ω T)) := by
    rw [Ideal.map_map, hcomp]
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := Ω)
    T (MvPolynomial (Fin 4) Ω) T P).trans
      (Ideal.quotientEquivAlg (P.map ι)
        (P.map (MvPolynomial.map (algebraMap Ω T))) b hmap.symm)

/-- The transport sends the literal tensor of a quotient polynomial to its
literal coefficient image multiplied by the actual tensor scalar. -/
theorem polynomialCoefficientQuotientTensorEquiv_tmul
    (P : Ideal (MvPolynomial (Fin 4) Ω)) (t : T) (q : MvPolynomial (Fin 4) Ω) :
    polynomialCoefficientQuotientTensorEquiv P (t ⊗ₜ[Ω] Ideal.Quotient.mk P q) =
      Ideal.Quotient.mk (P.map (MvPolynomial.map (algebraMap Ω T)))
        (t • MvPolynomial.map (algebraMap Ω T) q) := by
  let b := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) Ω T
  let ι : MvPolynomial (Fin 4) Ω →+* T ⊗[Ω] MvPolynomial (Fin 4) Ω :=
    (Algebra.TensorProduct.includeRight (R := Ω) (A := T)).toRingHom
  have hcomp : b.toRingHom.comp ι = MvPolynomial.map (algebraMap Ω T) := by
    apply RingHom.ext
    intro r
    change b (1 ⊗ₜ[Ω] r) = MvPolynomial.map (algebraMap Ω T) r
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  have hmap : (P.map ι).map b.toRingHom = P.map (MvPolynomial.map (algebraMap Ω T)) := by
    rw [Ideal.map_map, hcomp]
  let e₀ := Algebra.TensorProduct.tensorQuotientEquiv (R := Ω)
    T (MvPolynomial (Fin 4) Ω) T P
  let e₁ := Ideal.quotientEquivAlg (P.map ι)
    (P.map (MvPolynomial.map (algebraMap Ω T))) b hmap.symm
  have h₀ : e₀ (t ⊗ₜ[Ω] Ideal.Quotient.mk P q) =
      Ideal.Quotient.mk (P.map ι) (t ⊗ₜ[Ω] q) := rfl
  have h₁ : e₁ (Ideal.Quotient.mk (P.map ι) (t ⊗ₜ[Ω] q)) =
      Ideal.Quotient.mk (P.map (MvPolynomial.map (algebraMap Ω T)))
        (b (t ⊗ₜ[Ω] q)) := rfl
  change e₁ (e₀ (t ⊗ₜ[Ω] Ideal.Quotient.mk P q)) = _
  calc
    e₁ (e₀ (t ⊗ₜ[Ω] Ideal.Quotient.mk P q)) =
        e₁ (Ideal.Quotient.mk (P.map ι) (t ⊗ₜ[Ω] q)) := congrArg e₁ h₀
    _ = Ideal.Quotient.mk (P.map (MvPolynomial.map (algebraMap Ω T)))
        (b (t ⊗ₜ[Ω] q)) := h₁
    _ = Ideal.Quotient.mk (P.map (MvPolynomial.map (algebraMap Ω T)))
        (t • MvPolynomial.map (algebraMap Ω T) q) :=
      congrArg (Ideal.Quotient.mk (P.map (MvPolynomial.map (algebraMap Ω T))))
        (MvPolynomial.algebraTensorAlgEquiv_tmul (R := Ω) (A := T) t q)

/-- A genuine whole polynomial prime over an algebraically closed field
remains prime under the literal coefficient map to ANY extension field.
No algebraicity, finite-dimensionality, prime-extension or GI premise is
supplied for T. The domain of the actual polynomial quotient is used. -/
theorem algClosedPolynomialPrime_coefficientExtension_isPrime
    [IsAlgClosed Ω] (P : Ideal (MvPolynomial (Fin 4) Ω)) [P.IsPrime] :
    (P.map (MvPolynomial.map (algebraMap Ω T))).IsPrime := by
  let A := MvPolynomial (Fin 4) Ω ⧸ P
  letI : IsDomain (A ⊗[Ω] T) :=
    algClosedFiniteTypeDomain_tensorProduct_isDomain (Ω := Ω) (A := A) (T := T)
  letI : IsDomain (T ⊗[Ω] A) :=
    (Algebra.TensorProduct.comm Ω T A).toMulEquiv.isDomain
  have hQ : IsDomain (MvPolynomial (Fin 4) T ⧸
      P.map (MvPolynomial.map (algebraMap Ω T))) :=
    (polynomialCoefficientQuotientTensorEquiv (T := T) P).symm.toMulEquiv.isDomain
  exact (Ideal.Quotient.isDomain_iff_prime
    (I := P.map (MvPolynomial.map (algebraMap Ω T)))).mp hQ

end PfaffianDescent.Coray
