import PfaffianDescent.VoisinRelativeFibreIdealBaseChangeChartMorph
import PfaffianDescent.ClosedImmersionIdealBaseChangeIsoPresentation

/-!
# Universal ideal comparison from an affine normalized parameter chart

An affine open in the parameter scheme induces an open in the constant
cubic-surface family. The Cartesian fibre square transports canonical ideal
base change from the actual affine fibre to the universal closed immersion.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

set_option backward.isDefEq.respectTransparency false in
theorem isIso_fixedCubicSurfaceEquationZeroLocus_universalIdealBaseChange_of_affineChart
    {K T U : Type u} [Field K] [CommRing T] [Algebra K T] [CommRing U]
    (g : T →+* U)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (s : Spec (.of T) ⟶ E) [IsOpenImmersion s]
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K T)))
    (j : Monomials (Fin 4) 3)
    (t : Spec (.of T) ⟶ Spec (.of (ParameterChartRing K (Fin 4) 3 j)))
    (heq : s ≫ h = t ≫ parameterChartι K (Fin 4) 3 j)
    (hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h)) :
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let cJ := projectiveCoefficientMap g J
      (coefficientChangedHomogeneousIdeal g J)
      (coefficientChangedHomogeneousIdeal_toIdeal g J)
    let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k
      (algebraMap K T) s hs
    let v := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s
    IsIso (closedImmersionIdealBaseChangeHom
      ((cJ ≫ eX.inv) ≫ v)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) := by
  let J := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  let cJ := projectiveCoefficientMap g J
    (coefficientChangedHomogeneousIdeal g J)
    (coefficientChangedHomogeneousIdeal_toIdeal g J)
  let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k
    (algebraMap K T) s hs
  let v := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s
  let jF := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s
  let z := pullback.fst (fixedCubicSurfaceEquationZeroLocusToParameters
    a ha k h) s
  haveI : IsOpenImmersion v := by infer_instance
  haveI : IsClosedImmersion jF :=
    fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion_general
      a ha k h s
  have H : IsPullback jF z v
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h) :=
    isPullback_fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h s
  haveI : IsIso (closedImmersionIdealBaseChangeHom (cJ ≫ eX.inv) jF) :=
    isIso_fixedCubicSurfaceEquationZeroLocusFibreIdealBaseChange_of_chartMorph
      g a ha k h hk s hs j t heq hflat
  exact isIso_closedImmersionIdealBaseChangeHom_of_openPullbackPresentation
    (cJ ≫ eX.inv) v jF
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h) z H

end PfaffianDescent
