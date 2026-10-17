import PfaffianDescent.VoisinArbitraryParameterUniversalIdealBaseChange
import PfaffianDescent.VoisinRelativeZeroLocusFlat

/-!
# Arbitrary-parameter ideal base change for the actual Voisin family

The nontrivial flat moving-cubic family satisfies the hypotheses of the
global canonical ideal base-change theorem for every scheme change of its
equation parameters.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem flatGradedNontrivialOpen_universalIdealBaseChange_anyParameter
    {K R : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r qRank : ℕ) (e : Fin (r + qRank) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = qRank)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    {Y : Scheme.{u}}
    (f : Y ⟶ flatGradedProjectiveFamilyNontrivialOpen
      J r qRank e hRank a ha ha0) :
    let E := flatGradedProjectiveFamilyNontrivialOpen
      J r qRank e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r qRank e hRank ha0
    IsIso (@closedImmersionIdealBaseChangeHom _ _ _
      (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) f)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)
      (fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion a ha k h)) := by
  let E := flatGradedProjectiveFamilyNontrivialOpen
    J r qRank e hRank a ha ha0
  let k : E ⟶ Spec (.of K) :=
    flatGradedProjectiveFamilyNontrivialOpenToBase
      J r qRank e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))
  let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
    flatGradedNontrivialOpenToGlobalParameters a ha J r qRank e hRank ha0
  have hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k :=
    flatGradedNontrivialOpenToGlobalParameters_toBase
      a ha J r qRank e hRank ha0
  have hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) :=
    flatGradedNontrivialRelativeZeroLocusToParameters_flat
      J r qRank e hRank a ha ha0
  exact fixedCubicSurfaceEquationZeroLocus_universalIdealBaseChange_anyParameter
    a ha k h hk hflat f

end PfaffianDescent
