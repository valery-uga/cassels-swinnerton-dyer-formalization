import PfaffianDescent.VoisinNormalizedAffineUniversalIdealComparison
import PfaffianDescent.VoisinSurfaceCoefficientIdealComparison

/-!
# Universal ideal comparison along the canonical surface-fibre restriction

The affine universal ideal theorem can be stated using the Cartesian
restriction of the constant cubic-surface family, rather than the explicit
projective coefficient map that was used to prove it.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

set_option backward.isDefEq.respectTransparency false in
theorem fixedCubicParameterChartAffineCover_canonicalUniversalIdealBaseChange
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
    let b := algebraMap K T
    let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f j
    let hs : s ≫ k = Spec.map (CommRingCat.ofHom b) :=
      fixedCubicParameterChartAffineCover_toBase k h j
    let J := equationIdeal (a.map b) (ha.map b)
    let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
    let sg := Spec.map (CommRingCat.ofHom g) ≫ s
    let hsg := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
    let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b) sg hsg
    let q := fixedCubicSurfaceFamilyFibreRestriction a ha k s g
    let v := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s
    IsIso (closedImmersionIdealBaseChangeHom
      (((eqToHom (congrArg scheme hJ) ≫ eU.inv) ≫ q) ≫ v)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) := by
  let T := (fixedCubicParameterChartAffineCover h).X j
  letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h j
  let b := algebraMap K T
  let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f j
  let hs : s ≫ k = Spec.map (CommRingCat.ofHom b) :=
    fixedCubicParameterChartAffineCover_toBase k h j
  let J := equationIdeal (a.map b) (ha.map b)
  let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
  let sg := Spec.map (CommRingCat.ofHom g) ≫ s
  let hsg := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
  let eT := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
  let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b) sg hsg
  let q := fixedCubicSurfaceFamilyFibreRestriction a ha k s g
  let v := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s
  let cJ := projectiveCoefficientMap g J (coefficientChangedHomogeneousIdeal g J)
    (coefficientChangedHomogeneousIdeal_toIdeal g J)
  have hm := coefficientChangedSurfaceMap_toFamilyFibre_naturality
    a ha b g k s hs
  have hlocal := fixedCubicParameterChartAffineCover_universalIdealBaseChange
    a ha k h hk hflat j g
  change IsIso (closedImmersionIdealBaseChangeHom
    ((cJ ≫ eT.inv) ≫ v)
    (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) at hlocal
  rw [hm] at hlocal
  exact hlocal

end PfaffianDescent
