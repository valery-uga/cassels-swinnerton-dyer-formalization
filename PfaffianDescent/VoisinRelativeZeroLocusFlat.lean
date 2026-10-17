import PfaffianDescent.VoisinLocalRelativeFibreFlat
import PfaffianDescent.FlatOfTargetLocalTensor

/-!
# Global flatness of the moving cubic's relative zero locus

The actual relative universal-equation zero locus is flat over the
nontrivial moving-equation parameter family. The proof checks flatness
after passing to the local rings of each affine target chart, then uses
the target-local flatness criterion for schemes.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The relative universal zero locus on a smooth fixed cubic surface is
flat over Voisin's nontrivial moving-equation family. -/
theorem flatGradedNontrivialRelativeZeroLocusToParameters_flat
    {K R : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)] :
    Flat (flatGradedNontrivialRelativeZeroLocusToParameters
      a ha J r q e hRank ha0) := by
  let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
  let f := flatGradedNontrivialRelativeZeroLocusToParameters
    a ha J r q e hRank ha0
  apply flat_of_flat_targetAffineLocalFibres f
  intro i P hP
  let T := Localization P.primeCompl
  let n : Spec (.of T) ⟶ E :=
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(E.affineCover.X i, ⊤) T)) ≫
      (E.affineCover.X i).isoSpec.inv) ≫ E.affineCover.f i
  exact flatGradedNontrivialOpen_localSchemePoint_relativeFibre_flat
    J r q e hRank a ha ha0 n

end PfaffianDescent
