import PfaffianDescent.NativeWholeIdealComparisonDescent300
import PfaffianDescent.FiniteFlatBaseCoverDescent303

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Canonical local-family map, using the equality of WHOLE pulled-back ideals. -/
def nativeHilbertChartClosedFamilyMap300
    {X Xi : Scheme.{u}} (J : X.IdealSheafData) (d : Xi ⟶ X)
    (I : Xi.IdealSheafData) (h : J.comap d = I) : I.subscheme ⟶ J.subscheme :=
  (nativeClosedIdealComparisonIso300 J d I h).hom ≫ pullback.snd d J.subschemeι

/-- The local family lies in the genuine Cartesian restriction square. -/
lemma nativeHilbertChartClosedFamilyMap_isPullback300
    {X Xi B Bi : Scheme.{u}} (F : X ⟶ B) (d : Xi ⟶ X)
    (Fi : Xi ⟶ Bi) (b : Bi ⟶ B) (H : IsPullback d Fi F b)
    (J : X.IdealSheafData) (I : Xi.IdealSheafData) (h : J.comap d = I) :
    IsPullback (nativeHilbertChartClosedFamilyMap300 J d I h)
      (I.subschemeι ≫ Fi) (J.subschemeι ≫ F) b := by
  let e := nativeClosedIdealComparisonIso300 J d I h
  have Houter : IsPullback (pullback.snd d J.subschemeι)
      (pullback.fst d J.subschemeι ≫ Fi) (J.subschemeι ≫ F) b :=
    (IsPullback.of_hasPullback d J.subschemeι).flip.paste_vert H
  apply Houter.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [nativeHilbertChartClosedFamilyMap300, e, Iso.refl_hom,
      Category.comp_id]
  · simpa only [e, Iso.refl_hom, Category.comp_id, Category.assoc] using
      congrArg (fun f => f ≫ Fi) (nativeClosedIdealComparisonIso_hom_fst300 J d I h)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- A global whole ideal with these literal finite-flat chart restrictions
has finite-flat constant rank over the original base. -/
lemma nativeHilbertPoint_chartRestriction_properties300
    {X B : Scheme.{u}} (F : X ⟶ B) (U : B.OpenCover.{u})
    (Xi : U.I₀ → Scheme.{u}) (d : ∀ i, Xi i ⟶ X)
    (Fi : ∀ i, Xi i ⟶ U.X i)
    (H : ∀ i, IsPullback (d i) (Fi i) F (U.f i)) (n : ℕ)
    (P : ∀ i, FiniteFlatHilbertPoint195 (Fi i) n)
    (J : X.IdealSheafData) (hJ : ∀ i, J.comap (d i) = (P i).val) :
    IsFinite (J.subschemeι ≫ F) ∧ Flat (J.subschemeι ≫ F) ∧
      ∀ y, (J.subschemeι ≫ F).finrank y = n := by
  exact finiteFlat_rank_of_openCover_cartesian303 (J.subschemeι ≫ F) U
    (fun i => (P i).val.subscheme)
    (fun i => nativeHilbertChartClosedFamilyMap300 J (d i) (P i).val (hJ i))
    (fun i => (P i).val.subschemeι ≫ Fi i)
    (fun i => nativeHilbertChartClosedFamilyMap_isPullback300 F (d i) (Fi i)
      (U.f i) (H i) J (P i).val (hJ i)) n
    (fun i => (P i).property.1) (fun i => (P i).property.2.1)
    (fun i => (P i).property.2.2)

/-- The actual native test point, retaining the supplied global ideal literally.
The original construction below DERIVES that ideal and all these restrictions. -/
def nativeHilbertPointOfChartRestrictions300
    {X B : Scheme.{u}} (F : X ⟶ B) (U : B.OpenCover.{u})
    (Xi : U.I₀ → Scheme.{u}) (d : ∀ i, Xi i ⟶ X)
    (Fi : ∀ i, Xi i ⟶ U.X i)
    (H : ∀ i, IsPullback (d i) (Fi i) F (U.f i)) (n : ℕ)
    (P : ∀ i, FiniteFlatHilbertPoint195 (Fi i) n)
    (J : X.IdealSheafData) (hJ : ∀ i, J.comap (d i) = (P i).val) :
    FiniteFlatHilbertPoint195 F n :=
  ⟨J, nativeHilbertPoint_chartRestriction_properties300 F U Xi d Fi H n P J hJ⟩

lemma nativeHilbertPointOfChartRestrictions_ideal300
    {X B : Scheme.{u}} (F : X ⟶ B) (U : B.OpenCover.{u})
    (Xi : U.I₀ → Scheme.{u}) (d : ∀ i, Xi i ⟶ X)
    (Fi : ∀ i, Xi i ⟶ U.X i)
    (H : ∀ i, IsPullback (d i) (Fi i) F (U.f i)) (n : ℕ)
    (P : ∀ i, FiniteFlatHilbertPoint195 (Fi i) n)
    (J : X.IdealSheafData) (hJ : ∀ i, J.comap (d i) = (P i).val) :
    (nativeHilbertPointOfChartRestrictions300 F U Xi d Fi H n P J hJ).val = J := rfl

/-- Equality is of the genuine native whole embedded Hilbert test points. -/
lemma nativeHilbertPointOfChartRestrictions_baseChange300
    {X B : Scheme.{u}} (F : X ⟶ B) (U : B.OpenCover.{u})
    (Xi : U.I₀ → Scheme.{u}) (d : ∀ i, Xi i ⟶ X)
    (Fi : ∀ i, Xi i ⟶ U.X i)
    (H : ∀ i, IsPullback (d i) (Fi i) F (U.f i)) (n : ℕ)
    (P : ∀ i, FiniteFlatHilbertPoint195 (Fi i) n)
    (J : X.IdealSheafData) (hJ : ∀ i, J.comap (d i) = (P i).val) (i : U.I₀) :
    finiteFlatHilbertBaseChange195 (d i) (Fi i) F (U.f i) (H i) n
      (nativeHilbertPointOfChartRestrictions300 F U Xi d Fi H n P J hJ) = P i := by
  apply Subtype.ext
  exact hJ i

end PfaffianDescent
end
