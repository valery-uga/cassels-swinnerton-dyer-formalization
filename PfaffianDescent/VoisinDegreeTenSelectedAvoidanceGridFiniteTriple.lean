import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridRegularTriple
import PfaffianDescent.TripleCompleteIntersectionLength
noncomputable section
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_finiteTriple_of_nativeAvoidance
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
    ∃ (q r : MvPolynomial (Fin 4) F) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q.eval₂ (algebraMap F A) x = 0 ∧ r.eval₂ (algebraMap F A) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q ∧
      (∀ y : MvPolynomial (Fin 4) F,
        r * y ∈ Ideal.span ({p, q} : Set _) → y ∈ Ideal.span ({p, q} : Set _)) ∧
      ∃ hfinite : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)),
        letI := hfinite
        AllCharacteristics.finiteSchemeRank
          (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 27 := by
  obtain ⟨q, r, hq, hqx, hq0, hrel, hr, hrx, hregular⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_regularTriple_of_nativeAvoidance p hp hp0 x hpx hA havoid
  let hfinite := triple_cubic_intersection_finite p q r hp hq hr hp0 hq0 hrel hregular
  refine ⟨q, r, hq, hr, hqx, hrx, hq0, hrel, hregular, hfinite, ?_⟩
  exact triple_cubic_intersection_length_twenty_seven p q r hp hq hr hp0 hq0 hrel hregular
end PfaffianDescent
