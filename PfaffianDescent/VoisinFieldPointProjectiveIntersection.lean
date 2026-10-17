import PfaffianDescent.VoisinFieldPointRegularTwoCubicFibre
import PfaffianDescent.AmbientCoefficientProductMono

/-!
# The actual field-point fibre as a two-cubic projective scheme

The regular moving cubic from a field point cuts out the actual relative
zero-locus fibre as the projective scheme of the sum of the two cubic
equation ideals. This strengthens the previous description as a fibre
product of two hypersurfaces inside ambient projective space times the
field spectrum.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K R S : Type u} [Field K] [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [Algebra K R] [Field S] [Algebra R S]
  [Algebra K S] [IsScalarTower K R S]
variable (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
variable [Module.Flat R (CoordinateRing J)]
variable (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
variable (hRank : ∀ x : PrimeSpectrum R,
  Module.rankAtStalk (grading J 3) x = q)
variable (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
variable (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
variable (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
variable [Smooth (hypersurfaceToBase (a.map (algebraMap K S))
  (ha.map (algebraMap K S)))]
variable (s : Spec (.of S) ⟶
  pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
    J r q e hRank a ha ha0)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
variable (hs : s ≫ pullback.snd
  (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0)
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) = 𝟙 _)

include J r q e hRank hmap ha0 s hs in
/-- The actual relative zero-locus field fibre is the projective scheme
defined by the fixed cubic and the same moving cubic whose normalized
equations are regular on every standard chart. -/
theorem flatGradedNontrivialRelativeZeroLocus_fieldPoint_projectiveIntersection_regularCharts :
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
      (j : Monomials (Fin 4) 3) (_hj : p.coeff j.1 ≠ 0),
      ∃ (_fibreIso : (pullback (flatGradedNontrivialRelativeZeroLocusToParameters
          a ha J r q e hRank ha0)
        (s ≫ pullback.fst
          (flatGradedProjectiveFamilyNontrivialOpenToBase
            J r q e hRank a ha ha0)
          (Spec.map (CommRingCat.ofHom (algebraMap R S))))) ≅
        scheme (equationIdeal (a.map (algebraMap K S))
          (ha.map (algebraMap K S)) ⊔ equationIdeal p hp)),
        p ∈ C.toIdeal ∧
        CubicIntersectionRegularOnCharts (a.map (algebraMap K S))
          (ha.map (algebraMap K S)) p hp := by
  obtain ⟨p, hp, j, hj, fibreIso, hpC, hcharts⟩ :=
    flatGradedNontrivialRelativeZeroLocus_fieldPoint_twoCubic_regularCharts
      J r q e hRank C hmap a ha ha0 s hs
  let intersectionIso := twoHypersurfaceCoefficientProductIso
    (algebraMap K S) (Fin 4)
    (a.map (algebraMap K S)) p
    (ha.map (algebraMap K S)) hp
  exact ⟨p, hp, j, hj, fibreIso ≪≫ intersectionIso.symm, hpC, hcharts⟩

end PfaffianDescent
