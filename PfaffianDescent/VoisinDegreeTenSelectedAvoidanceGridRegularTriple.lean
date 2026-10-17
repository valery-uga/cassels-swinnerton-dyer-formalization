import PfaffianDescent.VoisinSectionChoice
import PfaffianDescent.VoisinFiniteSubschemeSections
noncomputable section
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_regularTriple_of_nativeAvoidance
    {F A : Type u} [Field F] [Infinite F] [CommRing A] [Algebra F A]
    [FiniteDimensional F A]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (x : Fin 4 → A)
    (hpx : p.eval₂ (algebraMap F A) x = 0) (hA : finrank F A = 16)
    (havoid : ∀ q : MvPolynomial (Fin 4) F, q.IsHomogeneous 3 → IsRelPrime p q →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin 4) F ⧸ Ideal.span ({p, q} : Set _))
        (MvPolynomial (Fin 4) F ⧸ Ideal.span ({p, q} : Set _)),
        ∃ r ∈ homogeneousVanishingPolynomialSubmodule (K := F) (A := A)
          (sigma := Fin 4) x 3, Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) r ∉ P) :
    ∃ q r : MvPolynomial (Fin 4) F,
      q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap F A) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q ∧
      r.IsHomogeneous 3 ∧ r.eval₂ (algebraMap F A) x = 0 ∧
      ∀ y : MvPolynomial (Fin 4) F,
        r * y ∈ Ideal.span ({p, q} : Set _) → y ∈ Ideal.span ({p, q} : Set _) := by
  have hsections := cubic_degree_sixteen_vanishing_sections_finrank p hp hp0 x hpx hA
  obtain ⟨q, hq, hqx, hq0, hrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_nonzero p hp hp0 x hpx hsections
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  obtain ⟨r, hr, hrx, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_avoids_associatedPrimes p q x (havoid q hq hrel)
  exact ⟨q, r, hq, hqx, hq0, hrel, hr, hrx, hregular⟩
end PfaffianDescent
