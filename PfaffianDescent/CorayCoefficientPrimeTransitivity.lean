import PfaffianDescent.CorayPolynomialComponentContraction
import PfaffianDescent.GaloisFixedPolynomialCoefficientDescent
import Mathlib.RingTheory.Invariant.Basic

/-!
# Actual coefficient action and transitivity on extended prime components

The coefficient action is constructed using literal MvPolynomial.map. Fixed
polynomials descend through their actual coefficients, giving the native
invariant-ring property. Going down derives contractions of actual minimal
primes; native invariant-ring transitivity then produces the automorphism
carrying any such minimal prime to any other.

This does not identify projective geometric components, descend a stable ideal
to its stabilizer fixed field, or assert a minimal definition-field degree.
SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
open scoped Pointwise
universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The actual Galois coefficient action, with each polynomial acted on by the
literal coefficient-map ring homomorphism of its field automorphism. -/
@[instance_reducible]
def polynomialGaloisCoefficientAction :
    MulSemiringAction (E ≃ₐ[K] E) (MvPolynomial (Fin 4) E) where
  smul g p := MvPolynomial.map g.toRingHom p
  one_smul p := by
    change MvPolynomial.map (RingHom.id E) p = p
    exact MvPolynomial.map_id p
  mul_smul g h p := by
    change MvPolynomial.map (g * h).toRingHom p =
      MvPolynomial.map g.toRingHom (MvPolynomial.map h.toRingHom p)
    exact (MvPolynomial.map_map h.toRingHom g.toRingHom p).symm
  smul_zero g := (MvPolynomial.map g.toRingHom).map_zero
  smul_one g := (MvPolynomial.map g.toRingHom).map_one
  smul_add g p q := (MvPolynomial.map g.toRingHom).map_add p q
  smul_mul g p q := (MvPolynomial.map g.toRingHom).map_mul p q

attribute [local instance] polynomialGaloisCoefficientAction

/-- Compatibility with the SAME original polynomial ground ring action,
proved by coefficient automorphisms fixing original ground coefficients. -/
@[instance_reducible]
def polynomialGaloisCoefficientSmulCommClass :
    SMulCommClass (E ≃ₐ[K] E) (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) E) where
  smul_comm g q p := by
    have hground : MvPolynomial.map g.toRingHom
        (MvPolynomial.map (algebraMap K E) q) =
        MvPolynomial.map (algebraMap K E) q := by
      apply MvPolynomial.ext
      intro d
      simp only [MvPolynomial.coeff_map]
      exact g.commutes (q.coeff d)
    change MvPolynomial.map g.toRingHom (q • p) =
      q • MvPolynomial.map g.toRingHom p
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_def, map_mul]
    rw [hground]

attribute [local instance] polynomialGaloisCoefficientSmulCommClass

/-- The actual coefficient action has the native invariant-ring property:
every fixed polynomial is the literal coefficient extension of an original
polynomial. No polynomial lift or invariance certificate is supplied. -/
theorem polynomialGaloisCoefficient_isInvariant [IsGalois K E] :
    Algebra.IsInvariant (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E)
      (E ≃ₐ[K] E) where
  isInvariant p hp := by
    obtain ⟨q, hq⟩ := galois_fixed_polynomial_descends p (fun g => hp g)
    exact ⟨q, hq⟩

/-- Actual minimal primes over the literal extension of an original prime are
conjugate by a genuine coefficient automorphism. Equal contractions follow
from going down and minimality (packet004); transitivity follows from the
constructed coefficient invariants and the native invariant-ring theorem.
The output uses the literal ideal-map expression, not an opaque action. -/
theorem polynomialCoefficientExtension_minimalPrimes_conjugate
    [FiniteDimensional K E] [IsGalois K E]
    (I : Ideal (MvPolynomial (Fin 4) K)) [I.IsPrime]
    (P Q : Ideal (MvPolynomial (Fin 4) E))
    (hP : P ∈ (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes)
    (hQ : Q ∈ (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
    ∃ g : E ≃ₐ[K] E, Q = P.map (MvPolynomial.map g.toRingHom) := by
  letI : P.IsPrime := hP.1.1
  letI : Q.IsPrime := hQ.1.1
  letI : MulSemiringAction (E ≃ₐ[K] E) (MvPolynomial (Fin 4) E) :=
    polynomialGaloisCoefficientAction (K := K) (E := E)
  letI : Algebra.IsInvariant (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E)
      (E ≃ₐ[K] E) := polynomialGaloisCoefficient_isInvariant
  have hPQ : P.under (MvPolynomial (Fin 4) K) =
      Q.under (MvPolynomial (Fin 4) K) :=
    (polynomialCoefficientExtension_minimalPrime_comap_eq I P hP).trans
      (polynomialCoefficientExtension_minimalPrime_comap_eq I Q hQ).symm
  obtain ⟨g, hg⟩ := @Algebra.IsInvariant.exists_smul_of_under_eq
    (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E) (E ≃ₐ[K] E)
    _ _ (MvPolynomial.algebraMvPolynomial (R := K) (S := E) (σ := Fin 4))
    _ (polynomialGaloisCoefficientAction (K := K) (E := E))
    (polynomialGaloisCoefficient_isInvariant (K := K) (E := E))
    inferInstance (polynomialGaloisCoefficientSmulCommClass (K := K) (E := E))
    P Q hP.1.1 hQ.1.1 hPQ
  refine ⟨g, hg.trans ?_⟩
  change P.map (MulSemiringAction.toRingHom (E ≃ₐ[K] E)
    (MvPolynomial (Fin 4) E) g) = P.map (MvPolynomial.map g.toRingHom)
  congr 1

end PfaffianDescent.Coray
