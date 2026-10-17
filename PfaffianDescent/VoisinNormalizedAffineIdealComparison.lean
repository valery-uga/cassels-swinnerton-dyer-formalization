import PfaffianDescent.VoisinRelativeNormalizedSurfaceCover
import PfaffianDescent.VoisinRelativeFibreIdealBaseChangeChartMorph

/-!
# Ideal comparison on each normalized affine parameter member

The actual relative family's flatness and the normalized-chart factorization
give canonical ideal base change after any further change of the affine
member's coefficient ring.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

set_option backward.isDefEq.respectTransparency false in
theorem fixedCubicParameterChartAffineCover_idealBaseChange
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
    let i := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h s
    letI : IsClosedImmersion i :=
      fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion_general
        a ha k h s
    IsIso (closedImmersionIdealBaseChangeHom (cJ ≫ eX.inv) i) := by
  let T := (fixedCubicParameterChartAffineCover h).X j
  letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h j
  let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f j
  have hs : s ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K T)) :=
    fixedCubicParameterChartAffineCover_toBase k h j
  let t : Spec (.of T) ⟶
      Spec (.of (ParameterChartRing K (Fin 4) 3 j.1)) :=
    Spec.map (CommRingCat.ofHom
      (fixedCubicParameterChartAffineCover_coefficientMap h j))
  have heq : s ≫ h = t ≫ parameterChartι K (Fin 4) 3 j.1 :=
    fixedCubicParameterChartAffineCover_coefficientMap_factor h j
  exact isIso_fixedCubicSurfaceEquationZeroLocusFibreIdealBaseChange_of_chartMorph
    g a ha k h hk s hs j.1 t heq hflat

end PfaffianDescent
