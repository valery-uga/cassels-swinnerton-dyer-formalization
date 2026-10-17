import PfaffianDescent.VoisinActualFibreIdealBaseChangeFromRelativeFlat
import PfaffianDescent.VoisinRelativeZeroLocusFlat

/-!
# Arbitrary-parameter ideal base change on Voisin's actual flat family

The global flatness of the nontrivial moving-cubic zero locus supplies the
sole hypothesis of the actual-fibre ideal comparison. The fibre coefficient
ring and its further change are arbitrary commutative rings.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem flatGradedNontrivialOpen_actualFibreIdealBaseChange_any
    {K R T U : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [Algebra K T] [CommRing U]
    (g : T →+* U)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r qRank : ℕ) (e : Fin (r + qRank) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = qRank)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (s : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r qRank e hRank a ha ha0)
    (hs : s ≫ (flatGradedProjectiveFamilyNontrivialOpenToBase
          J r qRank e hRank a ha ha0 ≫
          Spec.map (CommRingCat.ofHom (algebraMap K R))) =
      Spec.map (CommRingCat.ofHom (algebraMap K T)))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ flatGradedNontrivialOpenToGlobalParameters
      a ha J r qRank e hRank ha0 =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) =
      algebraMap K T) :
    let E := flatGradedProjectiveFamilyNontrivialOpen
      J r qRank e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters
        a ha J r qRank e hRank ha0
    let Jₐ := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let cJ := projectiveCoefficientMap g Jₐ
      (coefficientChangedHomogeneousIdeal g Jₐ)
      (coefficientChangedHomogeneousIdeal_toIdeal g Jₐ)
    let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k
      (algebraMap K T) s hs
    let i := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h s
    letI : IsClosedImmersion i :=
      fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion
        a ha k h (algebraMap K T) s hs j f heq hb
    IsIso (closedImmersionIdealBaseChangeHom (cJ ≫ eX.inv) i) := by
  let E := flatGradedProjectiveFamilyNontrivialOpen
    J r qRank e hRank a ha ha0
  let k : E ⟶ Spec (.of K) :=
    flatGradedProjectiveFamilyNontrivialOpenToBase
      J r qRank e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))
  let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
    flatGradedNontrivialOpenToGlobalParameters
      a ha J r qRank e hRank ha0
  have hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters
      a ha k h) :=
    flatGradedNontrivialRelativeZeroLocusToParameters_flat
      J r qRank e hRank a ha ha0
  exact isIso_fixedCubicSurfaceEquationZeroLocusFibreIdealBaseChange_of_flatFamily
    g a ha k h s hs j f heq hb hflat

end PfaffianDescent
