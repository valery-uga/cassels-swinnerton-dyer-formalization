import PfaffianDescent.VoisinSectionRestriction
import PfaffianDescent.FiniteProjectiveCoordinates
import PfaffianDescent.FiniteSubschemeCompleteIntersection
import PfaffianDescent.VoisinSectionChoice
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-!
# Section spaces through finite subschemes of a cubic surface

This file applies the concrete homogeneous restriction maps to actual finite
closed subschemes.  The normalized homogeneous coordinates generate the
finite coordinate algebra, and the scheme-theoretic rank is its vector-space
dimension.  Thus the numerical section estimates in Voisin's argument apply
to the actual subschemes, not merely to abstract vector spaces.
-/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u

section
variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalized coordinates for a finite closed subscheme of a cubic surface:
they generate its finite coordinate algebra and satisfy the defining cubic. -/
theorem cubicFiniteSubscheme_coordinates
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ x : Fin 4 → Γ(Z, ⊤),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  let j : Z ⟶ scheme (equationIdeal p hp) := i
  haveI : IsClosedImmersion j := ‹IsClosedImmersion i›
  haveI : IsFinite (j ≫ toBase (equationIdeal p hp)) := by
    change IsFinite (i ≫ hypersurfaceToBase p hp)
    infer_instance
  obtain ⟨x, hxsurj, hx⟩ :=
    finite_projective_closed_subscheme_coordinates (equationIdeal p hp) j
  refine ⟨x, hxsurj, ?_⟩
  exact hx p 3 hp (Ideal.subset_span (Set.mem_singleton p))

/-- An actual length-sixteen closed subscheme on a cubic surface has at
least three cubic sections through it, modulo the surface equation. -/
theorem cubicFiniteSubscheme_degree_sixteen_sections
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x
        hpx := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hxsurj, hpx⟩ := cubicFiniteSubscheme_coordinates p hp i
  refine ⟨x, hpx, hxsurj, ?_⟩
  apply cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
  exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi

/-- A length-sixteen finite subscheme on a prime cubic surface has normalized
coordinates and a nonzero cubic through it which is regular modulo the
surface equation. This isolates the part of Voisin's first choice which is a
formal consequence of section dimensions and surface primeness; only
primeness of the intermediate cubic--cubic curve remains for the base-locus
argument. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_cubic_section_of_prime_surface
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell q : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx :=
    cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
      ((finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi)
  obtain ⟨q, hqhom, hqvan, hq0, hqrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_nonzero
      p hp hne x hpx hsections hprime
  exact ⟨x, ell, q, hxsurj, hell, hxell, hpx, hqhom, hqvan, hq0, hqrel⟩

/- The same length-sixteen selection also records the fibrewise-regular pair
   over the coefficient field.  This is the form used when the chosen cubic
   is later transported into a flat parameter family. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_section_of_prime_with_fibrewiseRegularPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell q : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      q ≠ 0 ∧ q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      IsRelPrime p q ∧
      AllCharacteristics.IsFibrewiseRegularPair
        (algebraMap K (MvPolynomial (Fin 4) K)) p q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx :=
    cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
      ((finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi)
  obtain ⟨q, hqhom, hqvan, hqnot, hqrel, hqpair⟩ :=
    exists_regular_cubic_section_data_of_prime_with_fibrewiseRegularPair
      p hp hne x hpx hsections hprime
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hqnot
    rw [hzero]
    exact Ideal.zero_mem _
  exact ⟨x, ell, q, hxsurj, hell, hxell, hpx, hqhom, hqvan, hq0, hqnot,
    hqrel, hqpair⟩

/-- An actual length-eleven closed subscheme on a cubic surface has at least
eight cubic sections through it, modulo the surface equation. -/
theorem cubicFiniteSubscheme_degree_eleven_sections
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 11) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      8 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x
        hpx := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hxsurj, hpx⟩ := cubicFiniteSubscheme_coordinates p hp i
  refine ⟨x, hpx, hxsurj, ?_⟩
  apply cubic_degree_eleven_vanishing_sections_finrank p hp hne x hpx
  exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi

/-- For an actual length-eleven subscheme of a cubic surface, quadratic
restriction is not surjective.  This is precisely the dimension-count step
that supplies the nonzero cokernel in Voisin's Serre argument. -/
theorem cubicFiniteSubscheme_degree_eleven_quadratic_restriction_not_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 11) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ x : Fin 4 → Γ(Z, ⊤),
      p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ¬ Function.Surjective
        (homogeneousSectionRestriction (K := K) x 2) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hxsurj, hpx⟩ := cubicFiniteSubscheme_coordinates p hp i
  refine ⟨x, hpx, hxsurj, ?_⟩
  apply quadric_degree_eleven_restriction_not_surjective x
  exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi

/- A length-sixteen subscheme therefore admits an actual independent cubic
frame whose first member is the defining equation. -/
theorem cubicFiniteSubscheme_degree_sixteen_frame
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ v : Fin 4 →
          LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
        v 0 = cubicEquationKernelVector p hp x hpx ∧ LinearIndependent K v := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_sixteen_sections p hp hne i hi
  obtain ⟨v, hv0, hli⟩ := choose_cubic_vanishing_frame p hp hne x hpx hsections
  exact ⟨x, hpx, hxsurj, v, hv0, hli⟩

/- A length-sixteen subscheme also admits a regular cubic section whenever
the corresponding homogeneous linear system avoids the associated primes of
the surface quotient.  This packages the dimension, frame, and regularity
certificates in the single form consumed by the residual construction. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_section
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ((∀ P ∈ associatedPrimes
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))),
        ∃ q ∈ homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3,
          Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) q ∉ P) →
      (∃ v : Fin 4 →
          LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
        v 0 = cubicEquationKernelVector p hp x hpx ∧ LinearIndependent K v ∧
        ∃ q : MvPolynomial (Fin 4) K,
          q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q)) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_sixteen_sections p hp hne i hi
  refine ⟨x, hpx, hxsurj, ?_⟩
  intro havoid
  obtain ⟨v, hv0, hli⟩ :=
    choose_cubic_vanishing_frame p hp hne x hpx hsections
  obtain ⟨q, hqhom, hqvan, hqrel⟩ :=
    exists_regular_cubic_section_data p hp hne x hpx havoid
  exact ⟨v, hv0, hli, q, hqhom, hqvan, hqrel⟩

/- If the surface equation generates a prime ideal, the noncontainment supplied
by the frame turns the same certificate into an unconditional regular-section
choice for that intermediate prime. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_section_of_prime
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_sixteen_sections p hp hne i hi
  obtain ⟨q, hqhom, hqvan, _, hqrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_nonzero
      p hp hne x hpx hsections hprime
  exact ⟨x, hpx, hxsurj, q, hqhom, hqvan, hqrel⟩

/-- At the length-sixteen stage of a smooth cubic, the surface primeness used
to choose the first regular cubic section is automatic. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_section_of_smooth_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q := by
  exact cubicFiniteSubscheme_degree_sixteen_regular_section_of_prime p hp hne i hi
    (principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne))

/- The length-sixteen cubic stage can instead use the precise quotient
   rank-drop criterion for the selected linear system. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_section_of_finrank_drop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hdrop₂ :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3
      let q : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) :=
        (Ideal.Quotient.mkₐ K (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))).toLinearMap
      let V : Submodule K
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) := W.map q
      ∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ v : Fin 4 → LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
        v 0 = cubicEquationKernelVector p hp x hpx ∧ LinearIndependent K v ∧
        ∃ q : MvPolynomial (Fin 4) K,
          q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_sixteen_sections p hp hne i hi
  obtain ⟨v, hv0, hli⟩ := choose_cubic_vanishing_frame p hp hne x hpx hsections
  obtain ⟨q, hqhom, hqvan, _, hqrel⟩ :=
    exists_regular_cubic_section_data_of_finrank_drop p hp hne x hpx
      (hdrop₂ x hxsurj)
  exact ⟨x, hpx, hxsurj, v, hv0, hli, q, hqhom, hqvan, hqrel⟩

/- The first cubic section can be followed by a third section selected from
the quotient by the two chosen equations.  This is the complete three-cubic
certificate needed before invoking the length-27 residual calculation. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_triple_of_finrank_drop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hdrop₂ :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3
      let q : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) :=
        (Ideal.Quotient.mkₐ K (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))).toLinearMap
      let V : Submodule K
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) := W.map q
      ∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V)
    (hdrop₃ :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      ∀ (q : MvPolynomial (Fin 4) K),
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3
      let qmap : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
          (MvPolynomial (Fin 4) K ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q r : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 3 ∧ r.IsHomogeneous 3 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, v, hv0, hli, q, hqhom, hqvan, hqrel⟩ :=
    cubicFiniteSubscheme_degree_sixteen_regular_section_of_finrank_drop
      p hp hne i hi hdrop₂
  obtain ⟨r, hrhom, hrvan, hrreg⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop p q x
      (hdrop₃ x hxsurj q)
  exact ⟨x, hpx, hxsurj, q, r, hqhom, hrhom, hqvan, hrvan, hqrel, hrreg⟩

/- A finite family of possible first cubics can be handled at once.  The
   common vanishing system through the length-sixteen subscheme supplies one
   third cubic which is regular modulo every corresponding cubic--cubic ideal.
   This is the concrete finite-subscheme form of the simultaneous selector in
   `VoisinSectionChoice`; the geometric proof that a given family satisfies
   the rank-drop hypotheses remains an input from the base-locus argument. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_third_cubic_of_cubic_family_finrank_drop
    {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (Q : ι → MvPolynomial (Fin 4) K)
    (hdrop :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      ∀ j : ι,
      let I := Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3
      let qmap : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
          (MvPolynomial (Fin 4) K ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ r : MvPolynomial (Fin 4) K,
        r.IsHomogeneous 3 ∧ r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        ∀ j : ι, ∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, _⟩ :=
    cubicFiniteSubscheme_degree_sixteen_sections p hp hne i hi
  let I : ι → Ideal (MvPolynomial (Fin 4) K) := fun j =>
    Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K))
  obtain ⟨r, hrhom, hrvan, hrreg⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop_family x I (by
      intro j
      simpa only [I] using hdrop x hxsurj j)
  refine ⟨x, hpx, hxsurj, r, hrhom, hrvan, ?_⟩
  intro j y hy
  exact hrreg j y (by simpa only [I] using hy)

/- If the first two selected cubics generate a prime intermediate ideal, the
   frame dimension bound itself supplies the third regular cubic.  This
   packages the prime-intermediate branch separately from the associated-prime
   rank-drop branch above. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_triple_of_prime_intermediate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hprime₁ : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hprime₂ : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 3 →
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q r : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 3 ∧ r.IsHomogeneous 3 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_sixteen_sections p hp hne i hi
  obtain ⟨q, hqhom, hqvan, hqrel⟩ :=
    exists_regular_cubic_section_data_of_prime p hp hne x hpx hsections hprime₁
  obtain ⟨r, hrhom, hrvan, hrreg⟩ :=
    exists_regular_third_cubic_section_data_of_prime_and_sections
      p q x (hprime₂ q hqhom) hp hpx hqhom hqvan hsections
  exact ⟨x, hpx, hxsurj, q, r, hqhom, hrhom, hqvan, hrvan, hqrel, hrreg⟩

/- The prime-intermediate branch can retain the noncontainment witness for the
   first selected cubic.  In particular this exposes the nonzero hypothesis
   required by the complete-intersection residual theorem. -/
theorem cubicFiniteSubscheme_degree_sixteen_regular_triple_of_prime_intermediate_with_nonzero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hprime₁ : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hprime₂ : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 3 →
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q r : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 3 ∧ r.IsHomogeneous 3 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
        q ≠ 0 ∧
        IsRelPrime p q ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_sixteen_sections p hp hne i hi
  obtain ⟨q, hqhom, hqvan, hqnot, hqrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_not_mem p hp hne x hpx
      hsections hprime₁
  obtain ⟨r, hrhom, hrvan, hrreg⟩ :=
    exists_regular_third_cubic_section_data_of_prime_and_sections
      p q x (hprime₂ q hqhom) hp hpx hqhom hqvan hsections
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hqnot
    rw [hzero]
    exact Ideal.zero_mem _
  exact ⟨x, hpx, hxsurj, q, r, hqhom, hrhom, hqvan, hrvan, hqnot, hq0,
    hqrel, hrreg⟩

/- The same frame extraction applies to the length-eleven stage. -/
theorem cubicFiniteSubscheme_degree_eleven_frame
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 11) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ v : Fin 4 →
          LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
        v 0 = cubicEquationKernelVector p hp x hpx ∧ LinearIndependent K v := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eleven_sections p hp hne i hi
  have hsections' : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
    omega
  obtain ⟨v, hv0, hli⟩ := choose_cubic_vanishing_frame p hp hne x hpx hsections'
  exact ⟨x, hpx, hxsurj, v, hv0, hli⟩

/- The same bundled certificate is available at the length-eleven stage. -/
theorem cubicFiniteSubscheme_degree_eleven_regular_section
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 11) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ((∀ P ∈ associatedPrimes
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))),
        ∃ q ∈ homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3,
          Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) q ∉ P) →
      (∃ v : Fin 4 →
          LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
        v 0 = cubicEquationKernelVector p hp x hpx ∧ LinearIndependent K v ∧
        ∃ q : MvPolynomial (Fin 4) K,
          q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q)) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eleven_sections p hp hne i hi
  refine ⟨x, hpx, hxsurj, ?_⟩
  intro havoid
  have hsections' : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
    omega
  obtain ⟨v, hv0, hli⟩ :=
    choose_cubic_vanishing_frame p hp hne x hpx hsections'
  obtain ⟨q, hqhom, hqvan, hqrel⟩ :=
    exists_regular_cubic_section_data p hp hne x hpx havoid
  exact ⟨v, hv0, hli, q, hqhom, hqvan, hqrel⟩

/- The length-eleven residual stage has the identical prime-intermediate
specialization. -/
theorem cubicFiniteSubscheme_degree_eleven_regular_section_of_prime
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 11)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eleven_sections p hp hne i hi
  have hsections' : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
    omega
  obtain ⟨q, hqhom, hqvan, _, hqrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_nonzero
      p hp hne x hpx hsections' hprime
  exact ⟨x, hpx, hxsurj, q, hqhom, hqvan, hqrel⟩

/-- The analogous length-eleven regular-section choice on a smooth cubic
also needs no separately supplied prime-surface hypothesis. -/
theorem cubicFiniteSubscheme_degree_eleven_regular_section_of_smooth_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 11) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ IsRelPrime p q := by
  exact cubicFiniteSubscheme_degree_eleven_regular_section_of_prime p hp hne i hi
    (principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne))

/- The length-eleven cubic stage likewise accepts the exact quotient
   rank-drop estimate instead of a prime-intermediate shortcut. -/
theorem cubicFiniteSubscheme_degree_eleven_regular_section_of_finrank_drop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 11)
    (hdrop :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3
      let q : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) :=
        (Ideal.Quotient.mkₐ K (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))).toLinearMap
      let V : Submodule K
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) := W.map q
      ∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ v : Fin 4 → LinearMap.ker (homogeneousSectionRestriction (K := K) x 3),
        v 0 = cubicEquationKernelVector p hp x hpx ∧ LinearIndependent K v ∧
      ∃ q : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        IsRelPrime p q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eleven_sections p hp hne i hi
  have hsections' : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
    omega
  obtain ⟨v, hv0, hli⟩ := choose_cubic_vanishing_frame p hp hne x hpx hsections'
  obtain ⟨q, hqhom, hqvan, _, hqrel⟩ :=
    exists_regular_cubic_section_data_of_finrank_drop p hp hne x hpx
      (hdrop x hxsurj)
  exact ⟨x, hpx, hxsurj, v, hv0, hli, q, hqhom, hqvan, hqrel⟩

/-- An actual length-eight closed subscheme on a cubic surface has at least
two quadratic equations through it. -/
theorem cubicFiniteSubscheme_degree_eight_quadrics
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      2 ≤ finrank K (LinearMap.ker
        (homogeneousSectionRestriction (K := K) x 2)) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hxsurj, hpx⟩ := cubicFiniteSubscheme_coordinates p hp i
  refine ⟨x, hpx, hxsurj, ?_⟩
  apply quadric_degree_eight_vanishing_sections_finrank x
  exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi

/-- For a prime cubic equation, a length-eight closed subscheme has a nonzero
quadric through it which is relatively prime to the cubic.  Thus the first
quadric in the residual `8 → 4` construction needs no additional generic
choice once the cubic is known to be prime. -/
theorem cubicFiniteSubscheme_degree_eight_first_quadric_isRelPrime_of_prime_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpprime : Prime p)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eight_quadrics p hp i hi
  obtain ⟨q, hqhom, hqvan, hq0, hqrel⟩ :=
    exists_quadric_section_data_isRelPrime_of_prime_cubic p hp hpprime x hsections
  exact ⟨x, hpx, hxsurj, q, hqhom, hqvan, hq0, hqrel⟩

/-- The first quadric in Voisin's final residual can also retain the
normalized projective coordinates used by the complete-intersection
embedding. Surface primeness alone supplies this quadric; primeness of the
resulting cubic--quadric curve is the remaining geometric input. -/
theorem cubicFiniteSubscheme_degree_eight_regular_quadric_section_of_prime_surface
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell q : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  have hpprime : Prime p := (Ideal.span_singleton_prime hne).mp hprime
  obtain ⟨q, hqhom, hqvan, hq0, hqrel⟩ :=
    exists_quadric_section_data_isRelPrime_of_prime_cubic p hp hpprime x
      (quadric_degree_eight_vanishing_sections_finrank x
        ((finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi))
  exact ⟨x, ell, q, hxsurj, hell, hxell, hpx, hqhom, hqvan, hq0, hqrel⟩

/-- At the length-eight stage, one prime cubic--quadric intermediate
intersection is enough to select both quadrics with the regular-sequence
data needed for Voisin's residual construction.  The remaining geometric
input is exactly the existence of that prime intermediate curve. -/
theorem cubicFiniteSubscheme_degree_eight_regular_pair_of_prime_cubic_prime_first
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpprime : Prime p)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (hprime : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        ∃ q : MvPolynomial (Fin 4) K,
          q ∈ homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(Z, ⊤)) x 2 ∧ q ≠ 0 ∧
          (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (_hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q r : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 2 ∧ r.IsHomogeneous 2 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ q ≠ 0 ∧
        IsRelPrime p q ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eight_quadrics p hp i hi
  obtain ⟨q, r, hqhom, hrhom, hqvan, hrvan, hq0, hqrel, hrregular⟩ :=
    exists_regular_quadric_pair_data_of_prime_cubic_prime_first p hp hpprime x
      hsections (hprime x hxsurj)
  exact ⟨x, hpx, hxsurj, q, r, hqhom, hrhom, hqvan, hrvan, hq0, hqrel,
    hrregular⟩

/- A length-eight subscheme admits an actual independent pair of quadrics
through it. -/
theorem cubicFiniteSubscheme_degree_eight_quadric_pair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ v : Fin 2 →
          LinearMap.ker (homogeneousSectionRestriction (K := K) x 2),
        LinearIndependent K v := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eight_quadrics p hp i hi
  obtain ⟨v, hli⟩ := choose_quadric_vanishing_pair x hsections
  exact ⟨x, hpx, hxsurj, v, hli⟩

/- The length-eight certificate can be unpacked to two actual homogeneous
quadrics, each vanishing on the coordinate algebra. -/
theorem cubicFiniteSubscheme_degree_eight_quadric_pair_data
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ v : Fin 2 →
          LinearMap.ker (homogeneousSectionRestriction (K := K) x 2),
        LinearIndependent K v ∧
          ∀ j, (v j).1.1.IsHomogeneous 2 ∧
            (v j).1.1.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eight_quadrics p hp i hi
  obtain ⟨v, hli, hvdata⟩ := choose_quadric_vanishing_pair_data x hsections
  exact ⟨x, hpx, hxsurj, v, hli, hvdata⟩

/- If every nonzero quadratic section through the subscheme generates a
prime hypersurface ideal, one member of the independent pair can be chosen
relative-prime to a second quadratic section through the subscheme. -/
theorem cubicFiniteSubscheme_degree_eight_regular_quadric_of_prime
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (hprime : ∀ (q : MvPolynomial (Fin 4) K),
      q.IsHomogeneous 2 → q ≠ 0 →
      (Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q r : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 2 ∧ r.IsHomogeneous 2 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧ q ≠ 0 ∧ IsRelPrime q r := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, v, hli, hvdata⟩ :=
    cubicFiniteSubscheme_degree_eight_quadric_pair_data p hp i hi
  let q₀ : MvPolynomial (Fin 4) K := (v 0).1.1
  let q₁ : MvPolynomial (Fin 4) K := (v 1).1.1
  have hq₀hom := (hvdata 0).1
  have hq₁hom := (hvdata 1).1
  have hq₀van := (hvdata 0).2
  have hq₁van := (hvdata 1).2
  have hq₀ne : q₀ ≠ 0 := by
    intro hzero
    apply hli.ne_zero 0
    exact Subtype.ext (Subtype.ext hzero)
  have hq₁ne : q₁ ≠ 0 := by
    intro hzero
    apply hli.ne_zero 1
    exact Subtype.ext (Subtype.ext hzero)
  have hq₁_not_mem : q₁ ∉ Ideal.span ({q₀} : Set (MvPolynomial (Fin 4) K)) := by
    intro hmem
    have hdiv : q₀ ∣ q₁ := Ideal.mem_span_singleton.mp hmem
    obtain ⟨a, ha⟩ := homogeneous_dvd_same_degree_eq_smul
      hq₀hom hq₁hom hq₀ne hq₁ne hdiv
    have hpair : LinearIndependent K ![(v 0), (v 1)] := by
      convert hli using 1 <;> funext j <;> fin_cases j <;> rfl
    have hv₀ : v 0 ≠ 0 := hli.ne_zero 0
    have hpair_ne : ∀ b : K, b • (v 0) ≠ v 1 :=
      (LinearIndependent.pair_iff' (x := v 0) (y := v 1) hv₀).mp hpair
    apply hpair_ne a
    apply Subtype.ext
    apply Subtype.ext
    change a • q₀ = q₁
    exact ha.symm
  obtain ⟨r, hrvan, hrel⟩ :=
    exists_isRelPrime_in_linear_system_of_prime_ideal hq₀ne
      (hprime q₀ hq₀hom hq₀ne)
      (homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 2)
      ⟨q₁, ⟨v 1, (v 1).property, rfl⟩, hq₁_not_mem⟩
  obtain ⟨hrhom, hrvan'⟩ :=
    (mem_homogeneousVanishingPolynomialSubmodule_iff (K := K)
      (A := Γ(Z, ⊤)) (sigma := Fin 4) x 2 r).mp hrvan
  exact ⟨x, hpx, hxsurj, q₀, r, hq₀hom, hrhom, hq₀van, hrvan', hq₀ne, hrel⟩

/- A finite-dimensional rank-drop estimate for the quadratic system replaces
   the stronger assertion that every nonzero quadric is prime.  The ambient
   polynomial ring is a domain, so only the quotient associated-prime drops
   remain as geometric input. -/
theorem cubicFiniteSubscheme_degree_eight_regular_quadric_of_finrank_drop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (hdrop₂ :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      ∀ (f : MvPolynomial (Fin 4) K),
        f ∈ homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 2 →
        f ∈ nonZeroDivisors (MvPolynomial (Fin 4) K) →
        let I := Ideal.span ({f} : Set (MvPolynomial (Fin 4) K))
        let q : MvPolynomial (Fin 4) K →ₗ[K]
            MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
        let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) :=
          (homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 2).map q
        ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
            (MvPolynomial (Fin 4) K ⧸ I),
          Module.finrank K ((P.restrictScalars K).comap V.subtype) <
            Module.finrank K V) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (_hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q r : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 2 ∧ r.IsHomogeneous 2 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime q r := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eight_quadrics p hp i hi
  have hpos : 0 < Module.finrank K
      (homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 2) := by
    rw [homogeneousVanishingPolynomialSubmodule_finrank]
    omega
  obtain ⟨q, r, hqhom, hrhom, hqvan, hrvan, hq0, hrel⟩ :=
    exists_regular_homogeneous_pair_data_of_domain_finrank_drop_with_nonzero
      (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 2 hpos
      (hdrop₂ x hxsurj)
  exact ⟨x, hpx, hxsurj, q, r, hqhom, hrhom, hqvan, hrvan, hq0, hrel⟩

/- A finite family of possible first quadrics can be treated simultaneously.
   One quadratic section through the length-eight subscheme is regular modulo
   every corresponding cubic--quadric ideal.  This is the concrete endpoint
   form of `exists_regular_second_quadric_data_of_finrank_drop_family`. -/
theorem cubicFiniteSubscheme_degree_eight_regular_second_quadric_of_cubic_family_finrank_drop
    {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (Q : ι → MvPolynomial (Fin 4) K)
    (hdrop :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      ∀ j : ι,
      let I := Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 2
      let qmap : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
          (MvPolynomial (Fin 4) K ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (_hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ r : MvPolynomial (Fin 4) K,
        r.IsHomogeneous 2 ∧ r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        ∀ j : ι, ∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, _⟩ :=
    cubicFiniteSubscheme_degree_eight_quadrics p hp i hi
  let I : ι → Ideal (MvPolynomial (Fin 4) K) := fun j =>
    Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K))
  obtain ⟨r, hrhom, hrvan, hrreg⟩ :=
    exists_regular_second_quadric_data_of_finrank_drop_family x I (by
      intro j
      simpa only [I] using hdrop x hxsurj j)
  refine ⟨x, hpx, hxsurj, r, hrhom, hrvan, ?_⟩
  intro j y hy
  exact hrreg j y (by simpa only [I] using hy)

/- A still weaker quadratic interface asks only for one prime first member of
   the vanishing system.  The generic pair selector supplies the second
   relatively-prime quadric by dimension and prime avoidance. -/
theorem cubicFiniteSubscheme_degree_eight_regular_quadric_of_prime_first
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (hprime : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        ∃ q : MvPolynomial (Fin 4) K,
          q ∈ homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 2 ∧ q ≠ 0 ∧
          (Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤))
      (_hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ∃ q r : MvPolynomial (Fin 4) K,
        q.IsHomogeneous 2 ∧ r.IsHomogeneous 2 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime q r := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, hsections⟩ :=
    cubicFiniteSubscheme_degree_eight_quadrics p hp i hi
  obtain ⟨q, r, hqhom, hrhom, hqvan, hrvan, hq0, hrel⟩ :=
    exists_regular_homogeneous_pair_data_of_prime_first x 2 hsections
      (hprime x hxsurj)
  exact ⟨x, hpx, hxsurj, q, r, hqhom, hrhom, hqvan, hrvan, hq0, hrel⟩

end
end PfaffianDescent
