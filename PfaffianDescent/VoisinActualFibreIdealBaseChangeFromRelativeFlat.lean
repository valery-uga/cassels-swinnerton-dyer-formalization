import PfaffianDescent.VoisinRelativeFibreProjectiveFlatFromGlobal
import PfaffianDescent.ProjectiveQuotientRelativeGlobalIdealBaseChange
import PfaffianDescent.VoisinRelativeFibreCartier
import PfaffianDescent.ClosedImmersionIdealBaseChangeIsoPresentation

/-!
# Actual Voisin fibre ideal base change from relative flatness

The global relative-flatness theorem and the arbitrary-ring projective
fibre presentation imply canonical ideal base change for an actual fibre
under any further coefficient change, without a local-ring or residual-
regularity hypothesis on the fibre coefficient ring.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIso_fixedCubicSurfaceEquationZeroLocusFibreIdealBaseChange_of_flatFamily
    {K T U : Type u} [Field K] [CommRing T] [Algebra K T] [CommRing U]
    (g : T →+* U)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K T)))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) =
      algebraMap K T)
    (hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h)) :
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let cJ := projectiveCoefficientMap g J (coefficientChangedHomogeneousIdeal g J)
      (coefficientChangedHomogeneousIdeal_toIdeal g J)
    let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k
      (algebraMap K T) s hs
    let i := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h s
    letI : IsClosedImmersion i :=
      fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion
        a ha k h (algebraMap K T) s hs j f heq hb
    IsIso (closedImmersionIdealBaseChangeHom (cJ ≫ eX.inv) i) := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  let J := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  let cJ := projectiveCoefficientMap g J (coefficientChangedHomogeneousIdeal g J)
    (coefficientChangedHomogeneousIdeal_toIdeal g J)
  let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k
    (algebraMap K T) s hs
  let eZ := fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
    a ha k h (algebraMap K T) s hs j f heq hb
  let i := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s
  have hModel : IsClosedImmersion
      (normalizedTwoCubicToFixedCubic a ha (algebraMap K T) j f) := by
    unfold normalizedTwoCubicToFixedCubic
    exact schemeQuotientMap_closedImmersion _ _ _
  have hActual : IsClosedImmersion i :=
    fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion
      a ha k h (algebraMap K T) s hs j f heq hb
  have hProjectiveFlat : Flat (toBase (J ⊔ equationIdeal q hq)) :=
    fixedCubicSurfaceEquationZeroLocusProjectiveRingFibre_flat_of_flatFamily
      a ha k h (algebraMap K T) s hs j f heq hb hflat
  have hModelIso : IsIso (@closedImmersionIdealBaseChangeHom _ _ _ cJ
      (normalizedTwoCubicToFixedCubic a ha (algebraMap K T) j f) hModel) := by
    unfold normalizedTwoCubicToFixedCubic
    exact isIso_projectiveQuotient_globalIdealBaseChange_of_flatToBase
      g J (J ⊔ equationIdeal q hq)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)
      hProjectiveFlat
  have hsq : normalizedTwoCubicToFixedCubic
      a ha (algebraMap K T) j f ≫ eX.inv = eZ.inv ≫ i := by
    have h₀ := fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_immersionSquare
      a ha k h (algebraMap K T) s hs j f heq hb
    calc
      normalizedTwoCubicToFixedCubic a ha (algebraMap K T) j f ≫ eX.inv =
        eZ.inv ≫ (eZ.hom ≫
          normalizedTwoCubicToFixedCubic a ha (algebraMap K T) j f ≫ eX.inv) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = eZ.inv ≫ i := by rw [h₀]
  exact @isIso_closedImmersionIdealBaseChangeHom_of_isoPresentation
    _ _ _ _ _ cJ eX.symm
      (normalizedTwoCubicToFixedCubic a ha (algebraMap K T) j f)
      i hModel hActual eZ.symm hsq hModelIso

end PfaffianDescent
