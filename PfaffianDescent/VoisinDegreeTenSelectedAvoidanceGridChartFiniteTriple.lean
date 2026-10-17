import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridFiniteTriple
import PfaffianDescent.NormalizedChartAlgebraTransport
noncomputable section
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_chartFiniteTriple_of_nativeAvoidance
    {F A : Type u} [Field F] [Infinite F] [CommRing A] [Algebra F A]
    [FiniteDimensional F A]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (j : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) F))
    (hA : finrank F A = 16)
    (hchart : ∃ T : NormalizedAmbientChart F A (Fin 4)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) j,
      Function.Surjective (eval₂Hom (algebraMap F A) T.x) ∧
      p.eval₂ (algebraMap F A) T.x = 0 ∧
      ∀ q : MvPolynomial (Fin 4) F, q.IsHomogeneous 3 → IsRelPrime p q →
        ∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) F ⧸ Ideal.span ({p, q} : Set _))
          (MvPolynomial (Fin 4) F ⧸ Ideal.span ({p, q} : Set _)),
          ∃ r ∈ homogeneousVanishingPolynomialSubmodule (K := F) (A := A)
            (sigma := Fin 4) T.x 3, Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) r ∉ P) :
    ∃ (T : NormalizedAmbientChart F A (Fin 4)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) j)
      (q r : MvPolynomial (Fin 4) F) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      Function.Surjective (eval₂Hom (algebraMap F A) T.x) ∧
      p.eval₂ (algebraMap F A) T.x = 0 ∧
      q.eval₂ (algebraMap F A) T.x = 0 ∧ r.eval₂ (algebraMap F A) T.x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q ∧
      (∀ y : MvPolynomial (Fin 4) F,
        r * y ∈ Ideal.span ({p, q} : Set _) → y ∈ Ideal.span ({p, q} : Set _)) ∧
      ∃ hfinite : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)),
        letI := hfinite
        AllCharacteristics.finiteSchemeRank
          (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 27 := by
  obtain ⟨T, hxsurj, hpx, havoid⟩ := hchart
  obtain ⟨q, r, hq, hr, hqx, hrx, hq0, hrel, hregular, hfinite, h27⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_finiteTriple_of_nativeAvoidance p hp hp0 T.x hpx hA havoid
  exact ⟨T, q, r, hq, hr, hxsurj, hpx, hqx, hrx, hq0, hrel, hregular, hfinite, h27⟩
end PfaffianDescent
