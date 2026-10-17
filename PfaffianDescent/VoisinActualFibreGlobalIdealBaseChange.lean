import PfaffianDescent.ClosedImmersionIdealBaseChangeIsoPresentation
import PfaffianDescent.VoisinFixedCubicGlobalIdealBaseChange
import PfaffianDescent.VoisinRelativeFibreCartier
import PfaffianDescent.VoisinLocalPointGlobalIdealBaseChange

/-!
# Global ideal comparison on the actual relative Voisin fibre

The projective two-cubic model and the pullback-defined zero-locus
fibre are isomorphic as closed immersions. The canonical ideal-module
comparison therefore transfers from the explicit projective model
to the actual fibre, for any further coefficient change.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIso_fixedCubicSurfaceEquationZeroLocusFibreIdealBaseChange
    {K T U : Type u} [Field K] [CommRing T] [IsLocalRing T]
    [Algebra K T] [CommRing U]
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
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (((normalizedForm K (Fin 4) 3 j).map f).map
        (algebraMap T (IsLocalRing.ResidueField T))))) :
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
  have hModelIso : IsIso (@closedImmersionIdealBaseChangeHom _ _ _ cJ
      (normalizedTwoCubicToFixedCubic a ha (algebraMap K T) j f) hModel) := by
    exact isIso_fixedCubicGlobalIdealBaseChange_any g a ha q hq hreg
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

/-- At every local point of the actual nontrivial moving-cubic family,
there is a normalized chart for which the actual relative zero-locus
fibre has canonical ideal-module base change along any coefficient
ring map. -/
theorem flatGradedNontrivialOpen_localPoint_actualFibreIdealBaseChange_any
    {K R T U : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T] [Algebra R T]
    [Algebra K T] [IsScalarTower K R T] [CommRing U]
    (g : T →+* U)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r qRank : ℕ) (e : Fin (r + qRank) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = qRank)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T))))]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r qRank e hRank a ha ha0)
    (hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    let E := flatGradedProjectiveFamilyNontrivialOpen
      J r qRank e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters
        a ha J r qRank e hRank ha0
    ∃ (hs : n ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K T)))
      (j : Monomials (Fin 4) 3)
      (f : ParameterChartRing K (Fin 4) 3 j →+* T)
      (heq : n ≫ h =
        Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
      (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) =
        algebraMap K T),
      (let Jₐ := equationIdeal (a.map (algebraMap K T))
         (ha.map (algebraMap K T))
       let cJ := projectiveCoefficientMap g Jₐ
         (coefficientChangedHomogeneousIdeal g Jₐ)
         (coefficientChangedHomogeneousIdeal_toIdeal g Jₐ)
       let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k
         (algebraMap K T) n hs
       let i := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
         a ha k h n
       letI : IsClosedImmersion i :=
         fixedCubicSurfaceEquationZeroLocusFibre_isClosedImmersion
           a ha k h (algebraMap K T) n hs j f heq hb
       IsIso (closedImmersionIdealBaseChangeHom (cJ ≫ eX.inv) i)) := by
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
  have hs : n ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K T)) := by
    change n ≫ (flatGradedProjectiveFamilyNontrivialOpenToBase
      J r qRank e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))) = _
    rw [← Category.assoc, hn, ← Spec.map_comp]
    exact congrArg (fun φ : K →+* T => Spec.map (CommRingCat.ofHom φ))
      (IsScalarTower.algebraMap_eq K R T).symm
  obtain ⟨p, hp, j, hj, f, hf, hres, _hModelIso⟩ :=
    flatGradedNontrivialOpen_localPoint_exists_globalIdealBaseChange_any
      g J r qRank e hRank a ha ha0 n hn
  have heq : n ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫
        parameterChartι K (Fin 4) 3 j := hf.symm
  have hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) =
      algebraMap K T :=
    normalizedParameterChart_baseMap h k hk
      (algebraMap K T) n hs j f heq
  refine ⟨hs, j, f, heq, hb, ?_⟩
  exact isIso_fixedCubicSurfaceEquationZeroLocusFibreIdealBaseChange
    g a ha k h n hs j f heq hb hres

end PfaffianDescent
