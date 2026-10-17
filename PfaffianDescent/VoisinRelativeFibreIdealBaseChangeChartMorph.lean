import PfaffianDescent.VoisinActualFibreIdealBaseChangeFromRelativeFlat
import PfaffianDescent.VoisinRelativeFibreClosedImmersionGeneral

/-!
# Actual fibre ideal base change from a normalized chart morphism

The chart input is a scheme morphism. Its coefficient-ring map and
ground-field compatibility follow automatically from the chart diagram.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

theorem isIso_fixedCubicSurfaceEquationZeroLocusFibreIdealBaseChange_of_chartMorph
    {K T U : Type u} [Field K] [CommRing T] [Algebra K T] [CommRing U]
    (g : T →+* U)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (s : Spec (.of T) ⟶ E)
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
    let i := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h s
    letI : IsClosedImmersion i :=
      fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion_general
        a ha k h s
    IsIso (closedImmersionIdealBaseChangeHom (cJ ≫ eX.inv) i) := by
  let f : ParameterChartRing K (Fin 4) 3 j →+* T :=
    (Spec.preimage t).hom
  have ht : t = Spec.map (CommRingCat.ofHom f) :=
    (Spec.map_preimage t).symm
  have heqf : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫
        parameterChartι K (Fin 4) 3 j := by
    rw [← ht]
    exact heq
  have hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) =
      algebraMap K T :=
    normalizedParameterChart_baseMap h k hk
      (algebraMap K T) s hs j f heqf
  exact isIso_fixedCubicSurfaceEquationZeroLocusFibreIdealBaseChange_of_flatFamily
    g a ha k h s hs j f heqf hb hflat

end PfaffianDescent
