import PfaffianDescent.ProjectiveLinearSystem

/-!
# Homogeneous polynomial coordinates over a commutative ring

The Grassmannian charts used in Voisin's fixed-component argument are defined
over coordinate rings, not fields.  This file supplies the coefficient and
monomial-coordinate maps for a homogeneous polynomial piece over an arbitrary
commutative coefficient ring.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Finite σ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Extract the coefficients of a homogeneous degree-`d` polynomial in a
chosen enumeration of the degree-`d` monomials. -/
noncomputable def homogeneousCoefficientMapOverRing
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    homogeneousSubmodule σ R d →ₗ[R] (Fin m → R) where
  toFun q i := q.1.coeff (e i).1
  map_add' q r := by
    ext i
    simp
  map_smul' a q := by
    ext i
    simp [smul_eq_C_mul]

/-- Reconstruct a homogeneous degree-`d` polynomial from its monomial
coefficient vector over an arbitrary commutative ring. -/
noncomputable def homogeneousCoefficientSynthesisOverRing
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    (Fin m → R) →ₗ[R] homogeneousSubmodule σ R d where
  toFun c := ⟨∑ i, MvPolynomial.monomial (e i).1 (c i), by
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    exact MvPolynomial.isHomogeneous_monomial _ (e i).2⟩
  map_add' c c' := by
    apply Subtype.ext
    simp [Finset.sum_add_distrib]
  map_smul' a c := by
    apply Subtype.ext
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply,
      smul_eq_mul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (MvPolynomial.smul_monomial a).symm

/-- Coefficient synthesis followed by extraction is the identity. -/
theorem homogeneousCoefficientMapOverRing_synthesis
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    (homogeneousCoefficientMapOverRing d e).comp
      (homogeneousCoefficientSynthesisOverRing d e) =
        (LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R)) := by
  apply LinearMap.ext
  intro c
  funext i
  change (∑ j, MvPolynomial.monomial (e j).1 (c j)).coeff (e i).1 = c i
  rw [MvPolynomial.coeff_sum]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : (e j).1 ≠ (e i).1 := by
      intro h
      exact hji (e.injective (Subtype.ext h))
    simp [hne]
  · simp

/-- Extraction followed by coefficient synthesis is the identity on the
homogeneous degree-`d` part. -/
theorem homogeneousCoefficientSynthesisOverRing_map
    {m : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : homogeneousSubmodule σ R d) :
    homogeneousCoefficientSynthesisOverRing d e
      (homogeneousCoefficientMapOverRing d e q) = q := by
  apply Subtype.ext
  dsimp [homogeneousCoefficientSynthesisOverRing,
    homogeneousCoefficientMapOverRing]
  calc
    ∑ i : Fin m, MvPolynomial.monomial (e i).1 (q.1.coeff (e i).1) =
        ∑ i : Monomials σ d, MvPolynomial.monomial i.1 (q.1.coeff i.1) :=
      Fintype.sum_equiv e
        (fun i : Fin m => MvPolynomial.monomial (e i).1 (q.1.coeff (e i).1))
        (fun i : Monomials σ d => MvPolynomial.monomial i.1 (q.1.coeff i.1))
        (fun _ ↦ rfl)
    _ = q.1 := AllCharacteristics.UniversalHomogeneous.sum_monomial_coeff_eq q.1 q.2

/-- Synthesis after coefficient extraction is the identity as a linear map. -/
theorem homogeneousCoefficientSynthesisOverRing_comp_map
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    (homogeneousCoefficientSynthesisOverRing d e).comp
      (homogeneousCoefficientMapOverRing d e) =
        (LinearMap.id : homogeneousSubmodule σ R d →ₗ[R]
          homogeneousSubmodule σ R d) := by
  apply LinearMap.ext
  intro q
  exact homogeneousCoefficientSynthesisOverRing_map d e q

/-- The monomial-coordinate maps are mutually inverse linear equivalences
over any commutative coefficient ring. -/
noncomputable def homogeneousCoefficientLinearEquivOverRing
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    homogeneousSubmodule σ R d ≃ₗ[R] (Fin m → R) :=
  LinearEquiv.ofLinearMap (homogeneousCoefficientMapOverRing d e)
    (homogeneousCoefficientSynthesisOverRing d e)
    (homogeneousCoefficientMapOverRing_synthesis (R := R) d e)
    (homogeneousCoefficientSynthesisOverRing_comp_map (R := R) d e)

end PfaffianDescent
