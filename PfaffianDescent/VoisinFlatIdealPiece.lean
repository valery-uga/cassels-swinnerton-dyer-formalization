import PfaffianDescent.VoisinGenericGradeBaseChange

/-!
# Finite projective equation modules for flat projective models

The degreewise equations of a flat homogeneous projective model form a
direct summand of the finite free ambient polynomial piece. This is the
module-theoretic input for a Grassmannian family of the equations.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R : Type u} [CommRing R]
  (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R)) (n : ℕ)

/-- The quotient map from homogeneous polynomials of degree `n` to the
degree-`n` coordinate-ring piece. -/
noncomputable def homogeneousCoordinateQuotientMap :
    homogeneousSubmodule (Fin 4) R n →ₗ[R] grading J n :=
  ((Ideal.Quotient.mkₐ R J.toIdeal).toLinearMap.comp
    (homogeneousSubmodule (Fin 4) R n).subtype).codRestrict
      (grading J n) (by
        intro x
        change (Ideal.Quotient.mkₐ R J.toIdeal).toLinearMap x.1 ∈ grading J n
        exact ⟨x.1, x.2, rfl⟩)

theorem homogeneousCoordinateQuotientMap_surjective :
    Function.Surjective (homogeneousCoordinateQuotientMap J n) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := y.2
  refine ⟨⟨p, hp⟩, ?_⟩
  exact Subtype.ext hpy

/-- The equations of a projective model in a fixed degree, as the kernel
of the quotient map on homogeneous polynomials. -/
noncomputable def homogeneousModelIdealPiece :
    Submodule R (homogeneousSubmodule (Fin 4) R n) :=
  (homogeneousCoordinateQuotientMap J n).ker

theorem mem_homogeneousModelIdealPiece_iff
    (p : homogeneousSubmodule (Fin 4) R n) :
    p ∈ homogeneousModelIdealPiece J n ↔ p.1 ∈ J.toIdeal := by
  change (homogeneousCoordinateQuotientMap J n) p = 0 ↔ p.1 ∈ J.toIdeal
  simp [homogeneousCoordinateQuotientMap, Subtype.ext_iff,
    Ideal.Quotient.eq_zero_iff_mem]

/-- Every homogeneous polynomial piece is projective over the coefficient
ring, as a retract of the free polynomial module. -/
theorem homogeneousPolynomialPiece_projective :
    Module.Projective R (homogeneousSubmodule (Fin 4) R n) := by
  let H := homogeneousSubmodule (Fin 4) R n
  let r : MvPolynomial (Fin 4) R →ₗ[R] H :=
    (DFinsupp.lapply n).comp
      (DirectSum.decomposeLinearEquiv (homogeneousSubmodule (Fin 4) R)).toLinearMap
  apply Module.Projective.of_split H.subtype r
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  dsimp [r]
  change (DirectSum.decomposeLinearEquiv (homogeneousSubmodule (Fin 4) R)
    (x : MvPolynomial (Fin 4) R)) n = x
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  simp

/-- If the homogeneous coordinate ring is flat over a Noetherian base,
every fixed-degree ideal piece is finite projective. -/
theorem homogeneousModelIdealPiece_finite_projective
    [IsNoetherianRing R] [Module.Flat R (CoordinateRing J)] :
    Module.Finite R (homogeneousModelIdealPiece J n) ∧
      Module.Projective R (homogeneousModelIdealPiece J n) := by
  let q := homogeneousCoordinateQuotientMap J n
  letI : Module.Projective R (grading J n) :=
    coordinateRing_homogeneousPiece_projective J n
  letI : Module.Projective R (homogeneousSubmodule (Fin 4) R n) :=
    homogeneousPolynomialPiece_projective n
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (homogeneousCoordinateQuotientMap_surjective J n))
  let r : homogeneousSubmodule (Fin 4) R n →ₗ[R] q.ker :=
    (LinearMap.id - s.comp q).codRestrict q.ker (by
      intro x
      change q (x - s (q x)) = 0
      rw [map_sub]
      have hqs : q (s (q x)) = q x := by
        have h := LinearMap.congr_fun hs (q x)
        exact h
      rw [hqs, sub_self])
  have hr : r.comp q.ker.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (x : homogeneousSubmodule (Fin 4) R n) -
      s (q (x : homogeneousSubmodule (Fin 4) R n)) = x
    rw [x.property, map_zero, sub_zero]
  have hproj : Module.Projective R q.ker :=
    Module.Projective.of_split q.ker.subtype r hr
  have hfinite : Module.Finite R q.ker := by
    letI : Module.Finite R (homogeneousSubmodule (Fin 4) R n) :=
      Module.Finite.iff_fg.mpr
        (MvPolynomial.homogeneousSubmodule_fg (Fin 4) R n)
    apply Module.Finite.of_surjective r
    intro x
    refine ⟨(x : homogeneousSubmodule (Fin 4) R n), ?_⟩
    change r (q.ker.subtype x) = x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hr x
  exact ⟨hfinite, hproj⟩

end PfaffianDescent
