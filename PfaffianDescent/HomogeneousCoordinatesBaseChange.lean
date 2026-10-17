import PfaffianDescent.HomogeneousCoordinatesOverRing

/-!
# Base change for homogeneous coordinates

The homogeneous monomial-coordinate construction is compatible with arbitrary
maps of commutative coefficient rings.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  {σ : Type} [Finite σ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Apply a coefficient-ring homomorphism to a homogeneous polynomial. -/
noncomputable def homogeneousSubmoduleBaseChange (f : R →+* S) :
    homogeneousSubmodule σ R d →ₛₗ[f] homogeneousSubmodule σ S d where
  toFun q := ⟨MvPolynomial.map f q.1, q.2.map f⟩
  map_add' q q' := by
    apply Subtype.ext
    exact map_add (MvPolynomial.map f) q.1 q'.1
  map_smul' a q := by
    apply Subtype.ext
    change MvPolynomial.map f (a • q.1) = f a • MvPolynomial.map f q.1
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
      ← MvPolynomial.smul_eq_C_mul]

/-- Extend a system of homogeneous forms along a coefficient-ring map. -/
noncomputable def homogeneousSystemBaseChange (f : R →+* S)
    (W : Submodule R (homogeneousSubmodule σ R d)) :
    Submodule S (homogeneousSubmodule σ S d) :=
  Submodule.span S (homogeneousSubmoduleBaseChange d f '' (W : Set _))

/-- Coefficient extraction commutes with an arbitrary coefficient-ring map. -/
theorem homogeneousCoefficientMapOverRing_baseChange
    (f : R →+* S) {m : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : homogeneousSubmodule σ R d) :
    homogeneousCoefficientMapOverRing (R := S) d e
      (homogeneousSubmoduleBaseChange d f q) =
        fun i => f (homogeneousCoefficientMapOverRing (R := R) d e q i) := by
  funext i
  change (MvPolynomial.map f q.1).coeff (e i).1 = f (q.1.coeff (e i).1)
  exact MvPolynomial.coeff_map _ _ _

/-- Monomial synthesis commutes with an arbitrary coefficient-ring map. -/
theorem homogeneousCoefficientSynthesisOverRing_baseChange
    (f : R →+* S) {m : ℕ} (e : Fin m ≃ Monomials σ d)
    (c : Fin m → R) :
    homogeneousSubmoduleBaseChange d f
      (homogeneousCoefficientSynthesisOverRing (R := R) d e c) =
        homogeneousCoefficientSynthesisOverRing (R := S) d e (fun i => f (c i)) := by
  apply Subtype.ext
  change MvPolynomial.map f (∑ i, MvPolynomial.monomial (e i).1 (c i)) =
    ∑ i, MvPolynomial.monomial (e i).1 (f (c i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact MvPolynomial.map_monomial f (e i).1 (c i)

end PfaffianDescent
