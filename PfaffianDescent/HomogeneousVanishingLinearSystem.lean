import PfaffianDescent.VoisinSectionRestriction
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Homogeneous linear systems through finite coordinates

The restriction-map kernel is naturally a space of homogeneous forms rather
than a subspace of the whole polynomial ring.  Associated-prime avoidance is
most conveniently stated in the polynomial ring itself.  This file records
the injective image of that kernel and identifies its elements and dimension.
-/

namespace PfaffianDescent

open MvPolynomial Module

universe u v

section

variable {K A : Type u} {sigma : Type v} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A] [Fintype sigma]

/-- The `K`-linear system of degree-`d` homogeneous polynomials vanishing at
the given coordinates, regarded inside the whole multivariate polynomial
ring. -/
noncomputable def homogeneousVanishingPolynomialSubmodule
    (x : sigma → A) (d : ℕ) : Submodule K (MvPolynomial sigma K) :=
  (LinearMap.ker (homogeneousSectionRestriction (K := K) x d)).map
    (homogeneousSubmodule sigma K d).subtype

/- The source homogeneous piece is finite-dimensional, so its restriction
kernel and its polynomial image are finite-dimensional as well.  Recording
this instance lets codimension estimates be fed directly to the generic
associated-prime selector. -/
instance homogeneousVanishingPolynomialSubmodule_finiteDimensional
    (x : sigma → A) (d : ℕ) :
    FiniteDimensional K (homogeneousVanishingPolynomialSubmodule (K := K) x d) := by
  unfold homogeneousVanishingPolynomialSubmodule
  infer_instance

/- Positive finrank is the concrete nontriviality certificate needed by the
domain-specialized associated-prime selector. -/
theorem homogeneousVanishingPolynomialSubmodule_ne_bot_of_finrank_pos
    (x : sigma → A) (d : ℕ)
    (hpos : 0 < Module.finrank K
      (homogeneousVanishingPolynomialSubmodule (K := K) x d)) :
    homogeneousVanishingPolynomialSubmodule (K := K) x d ≠ ⊥ := by
  intro hbot
  have hzero : Module.finrank K
      (homogeneousVanishingPolynomialSubmodule (K := K) x d) = 0 := by
    rw [hbot]
    simp
  omega

/-- Membership in the concrete vanishing linear system means precisely
homogeneity of the prescribed degree and vanishing under evaluation. -/
theorem mem_homogeneousVanishingPolynomialSubmodule_iff
    (x : sigma → A) (d : ℕ) (q : MvPolynomial sigma K) :
    q ∈ homogeneousVanishingPolynomialSubmodule (K := K) x d ↔
      q.IsHomogeneous d ∧ q.eval₂ (algebraMap K A) x = 0 := by
  constructor
  · rintro ⟨qh, hqh, rfl⟩
    refine ⟨qh.property, ?_⟩
    change homogeneousSectionRestriction (K := K) x d qh = 0 at hqh
    change qh.val.eval₂ (algebraMap K A) x = 0 at hqh
    change qh.val.eval₂ (algebraMap K A) x = 0
    exact hqh
  · rintro ⟨hq, heval⟩
    let qh : homogeneousSubmodule sigma K d := ⟨q, hq⟩
    refine ⟨qh, ?_, rfl⟩
    change homogeneousSectionRestriction (K := K) x d qh = 0
    simpa only [homogeneousSectionRestriction_apply] using heval

/-- Passing from the restriction kernel to its polynomial realization loses
no dimension. -/
@[simp]
theorem homogeneousVanishingPolynomialSubmodule_finrank
    (x : sigma → A) (d : ℕ) :
    finrank K (homogeneousVanishingPolynomialSubmodule (K := K) x d) =
      finrank K (LinearMap.ker
        (homogeneousSectionRestriction (K := K) x d)) := by
  unfold homogeneousVanishingPolynomialSubmodule
  exact Submodule.finrank_map_subtype_eq
    (homogeneousSubmodule sigma K d)
    (LinearMap.ker (homogeneousSectionRestriction (K := K) x d))

end

end PfaffianDescent
