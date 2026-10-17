import PfaffianDescent.CorayComponentFiniteGaloisDefinition
import PfaffianDescent.CorayCoefficientPrimeTransitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Actual stable ideal descent to the component stabilizer fixed field

Trace-form coefficient projections remain in a stable ideal because their
extensions are sums of actual conjugates. An internally chosen trace dual
basis reconstructs every original polynomial. This descends the whole ideal,
without individually fixed generators or division by the extension degree.
The homogeneous component caller constructs its stabilizer and fixed field,
and derives the stability required for descent from those definitions.

No geometric component identification, minimal field-degree, genus, or divisor
descent result is asserted. SOURCE ONLY / UNVERIFIED: root alone compiles.
-/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open scoped Pointwise
universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Apply the actual trace pairing with a to every polynomial coefficient. -/
def galoisTraceCoefficientPolynomial (a : E) (q : MvPolynomial (Fin 4) E) :
    MvPolynomial (Fin 4) K :=
  (AddMonoidAlgebra.coeffLinearEquiv K (S := K) (M := Fin 4 →₀ ℕ)).symm
    ((Finsupp.mapRange.linearMap (Algebra.traceForm K E a))
      ((AddMonoidAlgebra.coeffLinearEquiv K (S := E) (M := Fin 4 →₀ ℕ)) q))

/-- Literal coefficients of the constructed trace polynomial. -/
theorem galoisTraceCoefficientPolynomial_coeff (a : E)
    (q : MvPolynomial (Fin 4) E) (d : Fin 4 →₀ ℕ) :
    coeff d (galoisTraceCoefficientPolynomial a q) =
      Algebra.trace K E (a * coeff d q) := rfl

/-- Extending the constructed trace polynomial gives the sum of actual
coefficient conjugates of the scalar multiple a*q. -/
theorem galoisTraceCoefficientPolynomial_map_eq_sum
    [FiniteDimensional K E] [IsGalois K E]
    (a : E) (q : MvPolynomial (Fin 4) E) :
    MvPolynomial.map (algebraMap K E) (galoisTraceCoefficientPolynomial a q) =
      ∑ g : E ≃ₐ[K] E, MvPolynomial.map g.toRingHom (C a * q) := by
  classical
  apply MvPolynomial.ext
  intro d
  simp only [coeff_map, galoisTraceCoefficientPolynomial_coeff, coeff_sum, coeff_C_mul]
  exact _root_.trace_eq_sum_automorphisms (K := K) (L := E) (a * coeff d q)

/-- Genuine finite Galois descent for an ENTIRE coefficient-stable polynomial
ideal. The original contraction extends back to exactly I. Stable generators,
trace splittings, a desired equality, and degree invertibility are not inputs. -/
theorem galois_stable_polynomial_ideal_map_comap
    [FiniteDimensional K E] [IsGalois K E]
    (I : Ideal (MvPolynomial (Fin 4) E))
    (hstable : ∀ g : E ≃ₐ[K] E, ∀ q ∈ I, MvPolynomial.map g.toRingHom q ∈ I) :
    (I.comap (MvPolynomial.map (algebraMap K E))).map
      (MvPolynomial.map (algebraMap K E)) = I := by
  classical
  let f : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) E :=
    MvPolynomial.map (algebraMap K E)
  let b := Module.finBasis K E
  apply le_antisymm Ideal.map_comap_le
  intro q hq
  have hprojectionI (a : E) : f (galoisTraceCoefficientPolynomial a q) ∈ I := by
    change MvPolynomial.map (algebraMap K E) (galoisTraceCoefficientPolynomial a q) ∈ I
    rw [galoisTraceCoefficientPolynomial_map_eq_sum]
    exact I.sum_mem fun g _ => hstable g (C a * q) (I.mul_mem_left _ hq)
  have hprojectionMap (a : E) :
      f (galoisTraceCoefficientPolynomial a q) ∈ (I.comap f).map f :=
    Ideal.mem_map_of_mem f (show galoisTraceCoefficientPolynomial a q ∈ I.comap f
      from hprojectionI a)
  have hdecomp : q = ∑ i : Fin (Module.finrank K E),
      C (b.traceDual i) * f (galoisTraceCoefficientPolynomial (b i) q) := by
    apply MvPolynomial.ext
    intro d
    dsimp only [f]
    simp only [coeff_sum, coeff_C_mul, coeff_map, galoisTraceCoefficientPolynomial_coeff]
    have h := b.traceDual.sum_repr (coeff d q)
    simp only [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
      Algebra.smul_def] at h
    simpa only [mul_comm] using h.symm
  rw [hdecomp]
  exact ((I.comap f).map f).sum_mem fun i _ =>
    ((I.comap f).map f).mul_mem_left _ (hprojectionMap (b i))

attribute [local instance] polynomialGaloisCoefficientAction
attribute [local instance] polynomialGaloisCoefficientSmulCommClass
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual coefficient-action stabilizer of a homogeneous ideal. -/
def homogeneousIdealCoefficientStabilizer
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E)) :
    Subgroup (E ≃ₐ[K] E) :=
  MulAction.stabilizer (E ≃ₐ[K] E) C.toIdeal

/-- The actual fixed intermediate field of that SAME ideal stabilizer. -/
abbrev homogeneousIdealStabilizerFixedField
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E)) :
    IntermediateField K E :=
  IntermediateField.fixedField (homogeneousIdealCoefficientStabilizer (K := K) C)

/-- An actual homogeneous prime descends to its actual coefficient stabilizer
fixed field. The whole ideal stability over that constructed field is derived
internally from the native subgroup/Galois-group equivalence; no stability or
stable-generator premise is supplied by the caller. The actual homogeneous
contraction is prime and its literal coefficient extension equals C. -/
theorem homogeneousPrime_stabilizerFixedField_descends
    [FiniteDimensional K E] [IsGalois K E]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E)) [C.toIdeal.IsPrime] :
    let L := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap L E))
    D.toIdeal.IsPrime ∧
      D.toIdeal.map (MvPolynomial.map (algebraMap L E)) = C.toIdeal := by
  classical
  let H := homogeneousIdealCoefficientStabilizer (K := K) C
  let L := homogeneousIdealStabilizerFixedField (K := K) C
  let e : H ≃* (E ≃ₐ[L] E) := IntermediateField.subgroupEquivAlgEquiv H
  have hstable : ∀ g : E ≃ₐ[L] E, ∀ q ∈ C.toIdeal,
      MvPolynomial.map g.toRingHom q ∈ C.toIdeal := by
    intro g q hq
    let h := e.symm g
    have hcoeff : (h : E ≃ₐ[K] E).toRingHom = g.toRingHom := by
      apply RingHom.ext
      intro a
      have hge : e h = g := e.apply_symm_apply g
      exact congrArg (fun φ : E ≃ₐ[L] E => φ a) hge
    have hstab : (h : E ≃ₐ[K] E) • C.toIdeal = C.toIdeal :=
      MulAction.mem_stabilizer_iff.mp h.2
    have hmem := Ideal.smul_mem_pointwise_smul (h : E ≃ₐ[K] E) q C.toIdeal hq
    rw [hstab] at hmem
    change MvPolynomial.map (h : E ≃ₐ[K] E).toRingHom q ∈ C.toIdeal at hmem
    rw [hcoeff] at hmem
    exact hmem
  refine ⟨inferInstance, ?_⟩
  exact galois_stable_polynomial_ideal_map_comap (K := L) (E := E) C.toIdeal hstable

end PfaffianDescent.Coray
