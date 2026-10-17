import PfaffianDescent.VoisinNormalizedAffineUniversalIdealComparison
import PfaffianDescent.VoisinRelativeZeroLocusFlat

/-!
# Universal ideal base change over every actual Voisin parameter chart

For the checked flat nontrivial moving-cubic family, the canonical ideal of
the universal zero locus commutes with every coefficient change starting
from a normalized affine parameter-cover member.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem flatGradedNontrivialOpen_affineUniversalIdealBaseChange_any
    {K R : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r qRank : ℕ) (e : Fin (r + qRank) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = qRank)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (j : (fixedCubicParameterChartAffineCover
      (flatGradedNontrivialOpenToGlobalParameters
        a ha J r qRank e hRank ha0)).I₀)
    {U : Type u} [CommRing U]
    (g : (fixedCubicParameterChartAffineCover
      (flatGradedNontrivialOpenToGlobalParameters
        a ha J r qRank e hRank ha0)).X j →+* U) :
    let E := flatGradedProjectiveFamilyNontrivialOpen
      J r qRank e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters
        a ha J r qRank e hRank ha0
    let T := (fixedCubicParameterChartAffineCover h).X j
    letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h j
    let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f j
    let hs : s ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K T)) :=
      fixedCubicParameterChartAffineCover_toBase k h j
    let Jₐ := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let cJ := projectiveCoefficientMap g Jₐ
      (coefficientChangedHomogeneousIdeal g Jₐ)
      (coefficientChangedHomogeneousIdeal_toIdeal g Jₐ)
    let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k
      (algebraMap K T) s hs
    let v := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s
    IsIso (closedImmersionIdealBaseChangeHom
      ((cJ ≫ eX.inv) ≫ v)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) := by
  let E := flatGradedProjectiveFamilyNontrivialOpen
    J r qRank e hRank a ha ha0
  let k : E ⟶ Spec (.of K) :=
    flatGradedProjectiveFamilyNontrivialOpenToBase
      J r qRank e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))
  let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
    flatGradedNontrivialOpenToGlobalParameters
      a ha J r qRank e hRank ha0
  have hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k :=
    flatGradedNontrivialOpenToGlobalParameters_toBase
      a ha J r qRank e hRank ha0
  have hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters
      a ha k h) :=
    flatGradedNontrivialRelativeZeroLocusToParameters_flat
      J r qRank e hRank a ha ha0
  exact fixedCubicParameterChartAffineCover_universalIdealBaseChange
    a ha k h hk hflat j g

end PfaffianDescent
