import PfaffianDescent.GroundTwistedCubicLiteralBinaryNineRestriction
import PfaffianDescent.CasselsOriginalPointContainingTwistedCubic
import PfaffianDescent.AmbientBottomProjectiveIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! SOURCE ONLY. The actual zero scheme of the ORIGINAL cubic under the
EXISTING original ground parametrization is the WHOLE original intersection.
Every scheme, ambient map and ideal is the original one. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- SAME actual ground parametrization and ORIGINAL ambient embedding. -/
def GroundTwistedCubicPresentation.actualAmbientParameterMap
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) :
    projectiveLineProj K ⟶ Proj PS :=
  hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B

/-- WHOLE original intersection maps to the ORIGINAL projective line
through the existing original curve Iso, with no new parametrization. -/
def GroundTwistedCubicPresentation.actualWholeIntersectionToOriginalLine
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (groundTwistedCubicCubicIntersectionIdeal B F hF) ⟶ projectiveLineProj K :=
  schemeQuotientMap B (groundTwistedCubicCubicIntersectionIdeal B F hF)
      (by change B.toIdeal ≤ (B ⊔ equationIdeal F hF).toIdeal
          rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) ≫
    hB.schemeIsoProjectiveLine.hom

/-- Transport the middle object of an actual Cartesian square by its
SAME Iso, before projective schemes or chosen ground maps are substituted. -/
private theorem originalRestrictionCartesian_transportIsoCut
    {C : Type*} [Category C] {W X Y Z X' : C}
    (a : W ⟶ X) (b : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback a b f g) (e : X ≅ X') :
    IsPullback (a ≫ e.hom) b (e.inv ≫ f) g := by
  apply h.of_iso (Iso.refl W) e (Iso.refl Y) (Iso.refl Z)
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, e.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The actual restricted-cubic zero square is Cartesian with the
ENTIRE original summed-ideal intersection, including its scheme structure. -/
theorem GroundTwistedCubicPresentation.actualRestrictedCubicCartesian
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    IsPullback (hB.actualWholeIntersectionToOriginalLine F hF)
      (PfaffianDescent.casselsTwistedCubicIntersectionToSurface B F hF)
      hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) := by
  exact originalRestrictionCartesian_transportIsoCut _ _ _ _
    (isPullback_projectiveIntersectionAmbient B (equationIdeal F hF))
    hB.schemeIsoProjectiveLine

/-- Canonical scheme Iso from the WHOLE original intersection to the
actual inverse-image zero scheme of the ORIGINAL cubic equation. -/
def GroundTwistedCubicPresentation.actualRestrictedCubicZeroSchemeIso
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (groundTwistedCubicCubicIntersectionIdeal B F hF) ≅
      pullback hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) :=
  (hB.actualRestrictedCubicCartesian F hF).isoPullback

/-- The original surface projection is retained EXACTLY by that Iso. -/
theorem GroundTwistedCubicPresentation.actualRestrictedCubicZeroSchemeIso_surface
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    (hB.actualRestrictedCubicZeroSchemeIso F hF).hom ≫
      pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) =
    PfaffianDescent.casselsTwistedCubicIntersectionToSurface B F hF :=
  (hB.actualRestrictedCubicCartesian F hF).isoPullback_hom_snd

/-- Finite rank transports through the SAME actual scheme Iso over its
original field base, before a curve/intersection/zero scheme is substituted. -/
private theorem originalRestrictionFiniteRank_isoCut
    {X Y : Scheme.{u}} (e : X ≅ Y)
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))
    [IsFinite pX] (hp : e.hom ≫ pY = pX) :
    ∃ hfinite : IsFinite pY,
      @AllCharacteristics.finiteSchemeRank K _ _ pY hfinite =
        AllCharacteristics.finiteSchemeRank pX := by
  have hpi : pY = e.inv ≫ pX := by
    have h := congrArg (fun z => e.inv ≫ z) hp
    simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp] using h
  letI : IsFinite pY := by rw [hpi]; infer_instance
  have hRank : AllCharacteristics.finiteSchemeRank pX =
      AllCharacteristics.finiteSchemeRank pY := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank,
      AllCharacteristics.finiteSchemeRank_eq_finrank, ← hp]
    exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom pY) _
  exact ⟨inferInstance, hRank.symm⟩

/-- Finiteness and actual rank nine of the SAME native restriction zero
scheme are DERIVED from the original whole intersection theorem. -/
theorem GroundTwistedCubicPresentation.actualRestrictedCubicZeroScheme_finite_rank_nine
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hnot : F ∉ B.toIdeal) :
    ∃ hfinite : IsFinite
        (pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) ≫
          hypersurfaceToBase F hF),
      @AllCharacteristics.finiteSchemeRank K _ _
        (pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) ≫
          hypersurfaceToBase F hF) hfinite = 9 := by
  obtain ⟨hfiniteW, hW⟩ := hB.cubicIntersection_finite_rank_nine_anyField F hF hnot
  letI := hfiniteW
  let e := hB.actualRestrictedCubicZeroSchemeIso F hF
  let p := pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) ≫
    hypersurfaceToBase F hF
  have hp : e.hom ≫ p = toBase (groundTwistedCubicCubicIntersectionIdeal B F hF) := by
    exact (Category.assoc e.hom
      (pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF))
      (hypersurfaceToBase F hF)).symm.trans
        ((congrArg (fun z => z ≫ hypersurfaceToBase F hF)
          (hB.actualRestrictedCubicZeroSchemeIso_surface F hF)).trans
          (PfaffianDescent.casselsTwistedCubicIntersectionToSurface_toBase B F hF))
  obtain ⟨hfiniteP, hRank⟩ := originalRestrictionFiniteRank_isoCut e
    (toBase (groundTwistedCubicCubicIntersectionIdeal B F hF)) p hp
  exact ⟨hfiniteP, hRank.trans hW⟩

end PfaffianDescent.QuarticNet
