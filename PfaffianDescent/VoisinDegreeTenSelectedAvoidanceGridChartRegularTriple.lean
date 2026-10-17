import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridRegularTriple
import PfaffianDescent.NormalizedChartAlgebraTransport
noncomputable section
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_chartRegularTriple_of_nativeAvoidance
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
      (q r : MvPolynomial (Fin 4) F),
      Function.Surjective (eval₂Hom (algebraMap F A) T.x) ∧
      p.eval₂ (algebraMap F A) T.x = 0 ∧
      q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap F A) T.x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q ∧
      r.IsHomogeneous 3 ∧ r.eval₂ (algebraMap F A) T.x = 0 ∧
      ∀ y : MvPolynomial (Fin 4) F,
        r * y ∈ Ideal.span ({p, q} : Set _) → y ∈ Ideal.span ({p, q} : Set _) := by
  obtain ⟨T, hxsurj, hpx, havoid⟩ := hchart
  obtain ⟨q, r, hq, hqx, hq0, hrel, hr, hrx, hregular⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_regularTriple_of_nativeAvoidance p hp hp0 T.x hpx hA havoid
  exact ⟨T, q, r, hxsurj, hpx, hq, hqx, hq0, hrel, hr, hrx, hregular⟩
end PfaffianDescent
