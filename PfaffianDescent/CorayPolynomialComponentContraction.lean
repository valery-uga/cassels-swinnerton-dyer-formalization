import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Actual polynomial coefficient flatness and component contraction

The literal coefficient extension is the native polynomial algebra pushout.
Field-extension flatness therefore supplies polynomial-extension flatness and
going down. Minimality then forces every minimal prime over an extended
original prime to contract to precisely that original prime.

No contraction equality, component transitivity, field of definition, or
geometric-integrality certificate is assumed.
SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
universe u v
variable {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Flatness of the literal polynomial coefficient-extension ring homomorphism,
constructed from the native polynomial pushout and field-extension flatness. -/
theorem polynomialCoefficientExtension_flat :
    (MvPolynomial.map (σ := Fin 4) (algebraMap K E)).Flat := by
  rw [← MvPolynomial.algebraMap_def, RingHom.flat_algebraMap_iff]
  exact Module.Flat.isBaseChange (R := K) (S := MvPolynomial (Fin 4) K)
    (M := E) (N := MvPolynomial (Fin 4) E)
    (Algebra.IsPushout.out (R := K) (S := MvPolynomial (Fin 4) K)
      (R' := E) (S' := MvPolynomial (Fin 4) E))

/-- Going down for the native polynomial algebra structure, whose actual
algebra map is definitionally the literal polynomial coefficient map. -/
theorem polynomialCoefficientExtension_hasGoingDown :
    Algebra.HasGoingDown (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E) := by
  letI : Module.Flat (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E) :=
    RingHom.flat_algebraMap_iff.mp
      (show (algebraMap (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E)).Flat
        from polynomialCoefficientExtension_flat (K := K) (E := E))
  infer_instance

/-- Every actual minimal prime of the coefficient extension of an original
prime contracts to that SAME original prime. Equal contractions are derived
internally by going down and minimality, with the exact polynomial map.
Neither finiteness nor a Galois hypothesis is needed for this algebra bridge. -/
theorem polynomialCoefficientExtension_minimalPrime_comap_eq
    (I : Ideal (MvPolynomial (Fin 4) K)) [I.IsPrime]
    (P : Ideal (MvPolynomial (Fin 4) E))
    (hP : P ∈ (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
    P.comap (MvPolynomial.map (algebraMap K E)) = I := by
  letI : Algebra.HasGoingDown (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E) :=
    polynomialCoefficientExtension_hasGoingDown (K := K) (E := E)
  letI : P.IsPrime := hP.1.1
  have hIP : I ≤ P.under (MvPolynomial (Fin 4) K) :=
    Ideal.map_le_iff_le_comap.mp hP.1.2
  obtain ⟨Q, hQP, hQprime, hQover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le
      (p := I) (q := P.under (MvPolynomial (Fin 4) K)) P hIP
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver I := hQover
  have hIQ : I.map (MvPolynomial.map (algebraMap K E)) ≤ Q := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact (Q.over_def I).le
  have hPQ : P ≤ Q := hP.2 ⟨hQprime, hIQ⟩ hQP
  have hQP_eq : Q = P := le_antisymm hQP hPQ
  change P.under (MvPolynomial (Fin 4) K) = I
  rw [← hQP_eq]
  exact (Q.over_def I).symm

end PfaffianDescent.Coray
