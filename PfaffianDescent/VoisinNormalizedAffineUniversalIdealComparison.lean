import PfaffianDescent.VoisinRelativeNormalizedSurfaceCover
import PfaffianDescent.VoisinUniversalIdealBaseChangeFromAffineChart

/-!
# Universal ideal comparison from every normalized affine parameter member

The canonical ideal of the universal relative zero locus commutes with
coefficient change starting at any member of the normalized affine cover.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

set_option backward.isDefEq.respectTransparency false in
theorem fixedCubicParameterChartAffineCover_universalIdealBaseChange
    {K : Type u} [Field K]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h))
    (j : (fixedCubicParameterChartAffineCover h).I₀)
    {U : Type u} [CommRing U]
    (g : (fixedCubicParameterChartAffineCover h).X j →+* U) :
    let T := (fixedCubicParameterChartAffineCover h).X j
    letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h j
    let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f j
    let hs : s ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K T)) :=
      fixedCubicParameterChartAffineCover_toBase k h j
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
  let T := (fixedCubicParameterChartAffineCover h).X j
  letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h j
  let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f j
  haveI : IsOpenImmersion s := (fixedCubicParameterChartAffineCover h).map_prop j
  have hs : s ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K T)) :=
    fixedCubicParameterChartAffineCover_toBase k h j
  let t : Spec (.of T) ⟶
      Spec (.of (ParameterChartRing K (Fin 4) 3 j.1)) :=
    Spec.map (CommRingCat.ofHom
      (fixedCubicParameterChartAffineCover_coefficientMap h j))
  have heq : s ≫ h = t ≫ parameterChartι K (Fin 4) 3 j.1 :=
    fixedCubicParameterChartAffineCover_coefficientMap_factor h j
  exact isIso_fixedCubicSurfaceEquationZeroLocus_universalIdealBaseChange_of_affineChart
    g a ha k h hk s hs j.1 t heq hflat

end PfaffianDescent
