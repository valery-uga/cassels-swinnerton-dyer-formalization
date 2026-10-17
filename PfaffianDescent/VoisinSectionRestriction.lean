import PfaffianDescent.VoisinSectionLinearAlgebra
import PfaffianDescent.HomogeneousProjection

/-!
# Restriction of homogeneous sections to a finite coordinate algebra

The numerical inequalities in Voisin's proof concern actual restriction
maps.  Given homogeneous coordinates with values in a finite algebra, this
file constructs those maps and proves the three kernel estimates used for a
cubic surface.  In degree three the defining cubic is divided out explicitly.
-/

namespace PfaffianDescent
open MvPolynomial Module
universe u

section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A]
variable {sigma : Type*} [Fintype sigma]

/-- Evaluation of degree-`d` homogeneous forms on homogeneous coordinates
with values in a finite `K`-algebra. -/
noncomputable def homogeneousSectionRestriction (x : sigma → A) (d : ℕ) :
    homogeneousSubmodule sigma K d →ₗ[K] A :=
  (eval₂AlgHom K x).toLinearMap.comp
    (homogeneousSubmodule sigma K d).subtype

@[simp]
lemma homogeneousSectionRestriction_apply (x : sigma → A) (d : ℕ)
    (q : homogeneousSubmodule sigma K d) :
    homogeneousSectionRestriction x d q = q.val.eval₂ (algebraMap K A) x := rfl

/-- The usual rank estimate for the concrete homogeneous restriction map. -/
theorem homogeneousSectionRestriction_kernel_lower_bound
    (x : sigma → A) (d target remaining : ℕ)
    (hsource : target + remaining ≤ finrank K (homogeneousSubmodule sigma K d))
    (htarget : finrank K A ≤ target) :
    remaining ≤ finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K) x d)) :=
  le_finrank_ker_of_target_bound (homogeneousSectionRestriction (K := K) x d)
    target remaining hsource htarget

end

section Cubic
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A]

/-- The defining cubic, regarded as a vector in the kernel of restriction to
a finite subscheme lying on that cubic. -/
noncomputable def cubicEquationKernelVector
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0) :
    LinearMap.ker (homogeneousSectionRestriction (K := K) x 3) :=
  ⟨⟨p, hp⟩, by simpa only [LinearMap.mem_ker, homogeneousSectionRestriction_apply]⟩

/-- The dimension of cubic sections vanishing on the finite coordinates,
after removing the one direction spanned by the defining equation. -/
noncomputable def cubicVanishingSectionsModuloEquationFinrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0) :=
  finrank K (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) - 1

/-- If restriction to the finite algebra leaves at least `r+1` cubic
equations, then at least `r` remain after quotienting by the surface
equation. -/
theorem cubicVanishingSectionsModuloEquation_finrank_lower_bound
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (target r : ℕ)
    (hsource : target + (r + 1) ≤
      finrank K (homogeneousSubmodule (Fin 4) K 3))
    (htarget : finrank K A ≤ target) :
    r ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
  have hker : r + 1 ≤ finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) :=
    homogeneousSectionRestriction_kernel_lower_bound (K := K) x 3 target (r + 1)
      hsource htarget
  unfold cubicVanishingSectionsModuloEquationFinrank
  omega

/-- A length-sixteen coordinate algebra on a cubic surface leaves at least
three independent cubic sections modulo the defining cubic. -/
theorem cubic_degree_sixteen_vanishing_sections_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hA : finrank K A = 16) :
    3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
  apply cubicVanishingSectionsModuloEquation_finrank_lower_bound
    p hp hne x hpx 16 3
  · rw [four_variable_homogeneous_finrank]
    decide
  · omega

/-- When a length-sixteen algebra receives every cubic section value, the
vanishing cubics form a four-dimensional space: three directions remain
after removing the surface equation. -/
theorem cubic_degree_sixteen_restriction_kernel_finrank_eq_four_of_surjective
    (x : Fin 4 → A) (hA : finrank K A = 16)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := K) x 3)) :
    finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K) x 3)) = 4 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (homogeneousSectionRestriction (K := K) x 3)
  have hrange : LinearMap.range
      (homogeneousSectionRestriction (K := K) x 3) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hsource : finrank K (homogeneousSubmodule (Fin 4) K 3) = 20 := by
    rw [four_variable_homogeneous_finrank]
    decide
  rw [hrange, finrank_top, hA, hsource] at hdim
  omega

/-- The four-dimensional kernel has dimension three modulo the cubic
surface equation. -/
theorem cubic_degree_sixteen_vanishing_sections_finrank_eq_three_of_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hA : finrank K A = 16)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := K) x 3)) :
    cubicVanishingSectionsModuloEquationFinrank p hp x hpx = 3 := by
  unfold cubicVanishingSectionsModuloEquationFinrank
  rw [cubic_degree_sixteen_restriction_kernel_finrank_eq_four_of_surjective
    x hA hsurj]

/-- A length-eleven coordinate algebra on a cubic surface leaves at least
eight independent cubic sections modulo the defining cubic. -/
theorem cubic_degree_eleven_vanishing_sections_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hA : finrank K A = 11) :
    8 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
  apply cubicVanishingSectionsModuloEquation_finrank_lower_bound
    p hp hne x hpx 11 8
  · rw [four_variable_homogeneous_finrank]
    decide
  · omega

/-- Quadratic sections cannot restrict surjectively to a coordinate algebra
of length eleven: their source has dimension ten.  This is the numerical
input in Voisin's degree-eleven Serre construction before the resulting
nonzero cokernel is identified with `H¹` of an ideal sheaf. -/
theorem quadric_degree_eleven_restriction_not_surjective
    (x : Fin 4 → A) (hA : finrank K A = 11) :
    ¬ Function.Surjective (homogeneousSectionRestriction (K := K) x 2) := by
  intro hsurj
  have hle := LinearMap.finrank_le_finrank_of_surjective
    (f := homogeneousSectionRestriction (K := K) x 2) hsurj
  have hsource : finrank K (homogeneousSubmodule (Fin 4) K 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  rw [hsource, hA] at hle
  omega

/-- A length-eight coordinate algebra leaves at least two quadratic forms
vanishing on it.  There is no surface equation to quotient out in degree two. -/
theorem quadric_degree_eight_vanishing_sections_finrank
    (x : Fin 4 → A) (hA : finrank K A = 8) :
    2 ≤ finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K) x 2)) := by
  apply homogeneousSectionRestriction_kernel_lower_bound (K := K) x 2 8 2
  · rw [four_variable_homogeneous_finrank]
    decide
  · omega

/-- If the eight finite conditions on quadratic sections are independent,
their vanishing system is exactly a pencil.  This is the rank-nullity form of
the first step in Voisin's degree-eight argument. -/
theorem quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
    (x : Fin 4 → A) (hA : finrank K A = 8)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := K) x 2)) :
    finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K) x 2)) = 2 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (homogeneousSectionRestriction (K := K) x 2)
  have hrange : LinearMap.range
      (homogeneousSectionRestriction (K := K) x 2) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hsource : finrank K (homogeneousSubmodule (Fin 4) K 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  rw [hrange, finrank_top, hA, hsource] at hdim
  omega

/-- For a length-eight coordinate algebra, the quadratic restrictions are
independent exactly when the vanishing quadratic system is a pencil.  Thus the
geometric rank-drop locus can be expressed equivalently as the locus where
this kernel has dimension greater than two. -/
theorem quadric_degree_eight_restriction_surjective_iff_kernel_finrank_eq_two
    (x : Fin 4 → A) (hA : finrank K A = 8) :
    Function.Surjective (homogeneousSectionRestriction (K := K) x 2) ↔
      finrank K (LinearMap.ker
        (homogeneousSectionRestriction (K := K) x 2)) = 2 := by
  constructor
  · exact quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective x hA
  · intro hker
    have hdim := LinearMap.finrank_range_add_finrank_ker
      (homogeneousSectionRestriction (K := K) x 2)
    have hsource : finrank K (homogeneousSubmodule (Fin 4) K 2) = 10 := by
      rw [four_variable_homogeneous_finrank]
      decide
    have hrange8 : finrank K (LinearMap.range
        (homogeneousSectionRestriction (K := K) x 2)) = 8 := by
      rw [hker, hsource] at hdim
      omega
    have hrange : finrank K (LinearMap.range
        (homogeneousSectionRestriction (K := K) x 2)) = finrank K A := by
      rw [hA]
      exact hrange8
    have htop : LinearMap.range (homogeneousSectionRestriction (K := K) x 2) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by simpa only [finrank_top] using hrange)
    exact LinearMap.range_eq_top.mp htop

end Cubic
end PfaffianDescent
