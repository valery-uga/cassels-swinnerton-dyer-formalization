import PfaffianDescent.GroundTwistedCubicBinaryNineNativeGlobalComparison
import PfaffianDescent.GroundTwistedCubicActualCubicRestrictionScheme

/-! SOURCE ONLY. Exact original ground projections and the binary
hypersurface versus ACTUAL pulled-back cubic zero scheme. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Evaluate a quotient equivalence by an explicit specialized lemma,
with the SAME canonical RingHom coercion in its ideal-image hypothesis. -/
private theorem quotientAlgEquiv_mkCut
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (e : A ≃ₐ[R] B)
    (h : J = I.map (e : A →+* B)) (x : A) :
    Ideal.quotientEquivAlg I J e h (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J (e x) :=
  Ideal.quotientEquivAlg_mk (I := I) (J := J) e h x

/-- Congruence for the dependent Proj map is proved before concrete
composed graded maps and their irrelevant-ideal witnesses are substituted. -/
private theorem projectiveMap_gradedHomCongrCut
    (I N : HomogeneousIdeal PS) (f g : grading I →+*ᵍ grading N)
    (hf : HomogeneousIdeal.irrelevant (grading N) ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant (grading I)))
    (hg : HomogeneousIdeal.irrelevant (grading N) ≤
      HomogeneousIdeal.map g (HomogeneousIdeal.irrelevant (grading I)))
    (h : f = g) : Proj.map f hf = Proj.map g hg := by
  cases h
  rfl

private theorem linearCoordinateChangeGradedHom_quotientNaturalityCut
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A.det)
    (I H J N : HomogeneousIdeal PS)
    (hIH : I.toIdeal ≤ H.toIdeal) (hJN : J.toIdeal ≤ N.toIdeal)
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv A hA).toRingHom)
    (hHN : N.toIdeal = H.toIdeal.map (linearSubstitutionEquiv A hA).toRingHom) :
    (linearCoordinateChangeGradedHom A hA H N hHN).comp
        (gradedQuotientMap I H hIH) =
      (gradedQuotientMap J N hJN).comp
        (linearCoordinateChangeGradedHom A hA I J hIJ) := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotientEquivAlg H.toIdeal N.toIdeal
      (linearSubstitutionEquiv A hA) hHN (Ideal.Quotient.mk H.toIdeal p) =
    Ideal.Quotient.factor hJN
      (Ideal.quotientEquivAlg I.toIdeal J.toIdeal
        (linearSubstitutionEquiv A hA) hIJ (Ideal.Quotient.mk I.toIdeal p))
  have hL := quotientAlgEquiv_mkCut H.toIdeal N.toIdeal
    (linearSubstitutionEquiv A hA)
    (show N.toIdeal = H.toIdeal.map
      (linearSubstitutionEquiv A hA : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K)
      from hHN) p
  have hR := quotientAlgEquiv_mkCut I.toIdeal J.toIdeal
    (linearSubstitutionEquiv A hA)
    (show J.toIdeal = I.toIdeal.map
      (linearSubstitutionEquiv A hA : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K)
      from hIJ) p
  exact hL.trans (congrArg (Ideal.Quotient.factor hJN) hR).symm

/-- Same actual GL coordinate change commutes with the ORIGINAL
homogeneous quotient immersion. No scheme square is assumed. -/
theorem linearCoordinateChangeSchemeIso_inv_quotientNaturality
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A.det)
    (I H J N : HomogeneousIdeal PS)
    (hIH : I.toIdeal ≤ H.toIdeal) (hJN : J.toIdeal ≤ N.toIdeal)
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv A hA).toRingHom)
    (hHN : N.toIdeal = H.toIdeal.map (linearSubstitutionEquiv A hA).toRingHom) :
    (linearCoordinateChangeSchemeIso A hA H N hHN).inv ≫ schemeQuotientMap I H hIH =
      schemeQuotientMap J N hJN ≫ (linearCoordinateChangeSchemeIso A hA I J hIJ).inv := by
  let f := linearCoordinateChangeGradedHom A hA H N hHN
  let g := linearCoordinateChangeGradedHom A hA I J hIJ
  let a := gradedQuotientMap I H hIH
  let b := gradedQuotientMap J N hJN
  have hf : Function.Surjective f :=
    (Ideal.quotientEquivAlg H.toIdeal N.toIdeal (linearSubstitutionEquiv A hA) hHN).surjective
  have hg : Function.Surjective g :=
    (Ideal.quotientEquivAlg I.toIdeal J.toIdeal (linearSubstitutionEquiv A hA) hIJ).surjective
  let hfm := gradedSurjective_irrelevant_le f hf
  let hgm := gradedSurjective_irrelevant_le g hg
  let ham := gradedSurjective_irrelevant_le a (gradedQuotientMap_surjective I H hIH)
  let hbm := gradedSurjective_irrelevant_le b (gradedQuotientMap_surjective J N hJN)
  have hc : f.comp a = b.comp g :=
    linearCoordinateChangeGradedHom_quotientNaturalityCut A hA I H J N hIH hJN hIJ hHN
  change Proj.map f hfm ≫ Proj.map a ham = Proj.map b hbm ≫ Proj.map g hgm
  rw [← Proj.map_comp a f ham hfm, ← Proj.map_comp g b hgm hbm]
  exact projectiveMap_gradedHomCongrCut I N (f.comp a) (b.comp g)
    (HomogeneousIdeal.irrelevant_le_map_comp ham hfm)
    (HomogeneousIdeal.irrelevant_le_map_comp hgm hbm) hc

namespace QuarticNet
open scoped MatrixGroups
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))

private theorem originalGroundProjection_composeCut
    {X V U C D T : Scheme.{u}}
    (f : X ⟶ V) (t : V ⟶ U) (q : U ⟶ C) (p : V ⟶ D)
    (e : D ⟶ C) (b : X ⟶ T) (v : T ⟶ D)
    (ht : t ≫ q = p ≫ e) (hf : f ≫ p = b ≫ v) :
    (f ≫ t) ≫ q = b ≫ (v ≫ e) := by
  calc
    (f ≫ t) ≫ q = f ≫ (t ≫ q) := Category.assoc f t q
    _ = f ≫ (p ≫ e) := congrArg (fun z => f ≫ z) ht
    _ = (f ≫ p) ≫ e := (Category.assoc f p e).symm
    _ = (b ≫ v) ≫ e := congrArg (fun z => z ≫ e) hf
    _ = b ≫ (v ≫ e) := Category.assoc b v e

private theorem actualRestrictionLine_composeCut
    {X W Y C T : Scheme.{u}} (a : X ≅ W) (z : W ≅ Y) (e : C ≅ T)
    (q : W ⟶ C) (b : X ⟶ T) (f : Y ⟶ T)
    (hz : z.hom ≫ f = q ≫ e.hom) (ha : a.hom ≫ q = b ≫ e.inv) :
    (a.hom ≫ z.hom) ≫ f = b := by
  calc
    (a.hom ≫ z.hom) ≫ f = a.hom ≫ (z.hom ≫ f) := Category.assoc _ _ _
    _ = a.hom ≫ (q ≫ e.hom) := congrArg (fun v => a.hom ≫ v) hz
    _ = (a.hom ≫ q) ≫ e.hom := (Category.assoc _ _ _).symm
    _ = (b ≫ e.inv) ≫ e.hom := congrArg (fun v => v ≫ e.hom) ha
    _ = b := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The literal binary-to-original-whole-intersection Iso preserves
EXACTLY the EXISTING chosen ground parametrization and original curve map. -/
theorem GroundTwistedCubicPresentation.literalBinaryNineOriginalWholeIntersectionIso_curve
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    let G := hB.literalRestrictedBinaryNine F hF
    (hB.literalBinaryNineOriginalWholeIntersectionIso F hF).hom ≫
        schemeQuotientMap B (groundTwistedCubicCubicIntersectionIdeal B F hF)
          (by change B.toIdeal ≤ (B ⊔ equationIdeal F hF).toIdeal
              rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) =
      schemeQuotientMap L (equationIdeal (G : MvPolynomial Bool K) G.property)
        (by exact bot_le) ≫ hB.schemeIsoProjectiveLine.inv := by
  let A : GL (Fin 4) K := Classical.choose hB
  have hdet : IsUnit ((A : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)
  let H := groundTwistedCubicCubicIntersectionIdeal B F hF
  let N := I ⊔ equationIdeal
    (linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F)
    (linearSubstitution_homogeneous (A : Matrix (Fin 4) (Fin 4) K) hF)
  have hBI : (I).toIdeal = B.toIdeal.map
      (linearSubstitutionEquiv (A : Matrix (Fin 4) (Fin 4) K) hdet).toRingHom :=
    (Classical.choose_spec hB).symm
  have hHN : N.toIdeal = H.toIdeal.map
      (linearSubstitutionEquiv (A : Matrix (Fin 4) (Fin 4) K) hdet).toRingHom :=
    groundTwistedCubicCubicIntersectionIdeal_coordinate_map B A
      (Classical.choose_spec hB) F hF hdet
  let eB := linearCoordinateChangeSchemeIso (A : Matrix (Fin 4) (Fin 4) K) hdet B I hBI
  let eH := linearCoordinateChangeSchemeIso (A : Matrix (Fin 4) (Fin 4) K) hdet H N hHN
  have hBH : B.toIdeal ≤ H.toIdeal := by
    change B.toIdeal ≤ (B ⊔ equationIdeal F hF).toIdeal
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  have hIN : (I).toIdeal ≤ N.toIdeal := by
    change (I).toIdeal ≤ (I ⊔ equationIdeal
      (linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F)
      (linearSubstitution_homogeneous (A : Matrix (Fin 4) (Fin 4) K) hF)).toIdeal
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  have hn := linearCoordinateChangeSchemeIso_inv_quotientNaturality
    (A : Matrix (Fin 4) (Fin 4) K) hdet B H I N hBH hIN hBI hHN
  have hStd : (hB.literalBinaryNineNativeGlobalIso F hF).hom ≫
      schemeQuotientMap I N hIN =
      schemeQuotientMap L
        (equationIdeal (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K)
          (hB.literalRestrictedBinaryNine F hF).property) (by exact bot_le) ≫
        standardProjectiveLineToTwistedCubic (K := K) :=
    hB.literalBinaryNineNativeGlobalIso_projection F hF
  change ((hB.literalBinaryNineNativeGlobalIso F hF).hom ≫ eH.inv) ≫
      schemeQuotientMap B H hBH =
    schemeQuotientMap L _ _ ≫ (standardProjectiveLineToTwistedCubic (K := K) ≫ eB.inv)
  exact originalGroundProjection_composeCut
    (hB.literalBinaryNineNativeGlobalIso F hF).hom eH.inv
    (schemeQuotientMap B H hBH) (schemeQuotientMap I N hIN) eB.inv
    (schemeQuotientMap L _ (by exact bot_le))
    (standardProjectiveLineToTwistedCubic (K := K)) hn hStd

/-- The actual homogeneous binary-nine hypersurface IS the original
cubic inverse-image zero scheme under the SAME native ground parametrization. -/
def GroundTwistedCubicPresentation.literalBinaryNineActualRestrictionIso
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    let G := hB.literalRestrictedBinaryNine F hF
    scheme (equationIdeal (G : MvPolynomial Bool K) G.property) ≅
      pullback hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) :=
  hB.literalBinaryNineOriginalWholeIntersectionIso F hF ≪≫
    hB.actualRestrictedCubicZeroSchemeIso F hF

/-- EXACT original binary hypersurface-to-line projection of the
actual restriction comparison, rather than a newly selected morphism. -/
theorem GroundTwistedCubicPresentation.literalBinaryNineActualRestrictionIso_line
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    let G := hB.literalRestrictedBinaryNine F hF
    (hB.literalBinaryNineActualRestrictionIso F hF).hom ≫
        pullback.fst hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) =
      schemeQuotientMap L (equationIdeal (G : MvPolynomial Bool K) G.property)
        (by exact bot_le) := by
  have hBH : B.toIdeal ≤ (groundTwistedCubicCubicIntersectionIdeal B F hF).toIdeal := by
    change B.toIdeal ≤ (B ⊔ equationIdeal F hF).toIdeal
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  let q := schemeQuotientMap B (groundTwistedCubicCubicIntersectionIdeal B F hF) hBH
  let b := schemeQuotientMap L
    (equationIdeal (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K)
      (hB.literalRestrictedBinaryNine F hF).property) (by exact bot_le)
  have hz : (hB.actualRestrictedCubicZeroSchemeIso F hF).hom ≫
      pullback.fst hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) =
      q ≫ hB.schemeIsoProjectiveLine.hom :=
    (hB.actualRestrictedCubicCartesian F hF).isoPullback_hom_fst
  have ha : (hB.literalBinaryNineOriginalWholeIntersectionIso F hF).hom ≫ q =
      b ≫ hB.schemeIsoProjectiveLine.inv :=
    hB.literalBinaryNineOriginalWholeIntersectionIso_curve F hF
  exact actualRestrictionLine_composeCut
    (hB.literalBinaryNineOriginalWholeIntersectionIso F hF)
    (hB.actualRestrictedCubicZeroSchemeIso F hF) hB.schemeIsoProjectiveLine q b
    (pullback.fst hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF)) hz ha

/-- EXACT original surface quotient projection, retaining the original
intersection's entire scheme structure under the SAME constructed Iso. -/
theorem GroundTwistedCubicPresentation.literalBinaryNineActualRestrictionIso_surface
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    (hB.literalBinaryNineActualRestrictionIso F hF).hom ≫
        pullback.snd hB.actualAmbientParameterMap (hypersurfaceToAmbient F hF) =
      (hB.literalBinaryNineOriginalWholeIntersectionIso F hF).hom ≫
        PfaffianDescent.casselsTwistedCubicIntersectionToSurface B F hF := by
  change ((hB.literalBinaryNineOriginalWholeIntersectionIso F hF).hom ≫
      (hB.actualRestrictedCubicZeroSchemeIso F hF).hom) ≫ _ = _
  rw [Category.assoc, hB.actualRestrictedCubicZeroSchemeIso_surface]

end QuarticNet
end PfaffianDescent
