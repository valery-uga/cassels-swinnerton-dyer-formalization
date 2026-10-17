import PfaffianDescent.GroundTwistedCubicBinaryNineNativeChartComparison
import Mathlib.AlgebraicGeometry.Gluing

/-! SOURCE ONLY. Glue the actual binary-hypersurface chart Isos by their
EXACT projection to the original standard curve. Whole schemes are retained. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem glueThroughMono_compatibleCut
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [Mono i]
    (c : Z.OpenCover) (f : ∀ a, c.X a ⟶ X) (h : Z ⟶ Y)
    (hf : ∀ a, f a ≫ i = c.f a ≫ h) (a b : c.I₀) :
    pullback.fst (c.f a) (c.f b) ≫ f a =
      pullback.snd (c.f a) (c.f b) ≫ f b := by
  apply (cancel_mono i).mp
  simp only [Category.assoc, hf]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ h) (pullback.condition (f := c.f a) (g := c.f b))

private def glueThroughMonoCut
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [Mono i]
    (c : Z.OpenCover) (f : ∀ a, c.X a ⟶ X) (h : Z ⟶ Y)
    (hf : ∀ a, f a ≫ i = c.f a ≫ h) : Z ⟶ X :=
  c.glueMorphisms f (glueThroughMono_compatibleCut i c f h hf)

private theorem glueThroughMonoCut_projection
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [Mono i]
    (c : Z.OpenCover) (f : ∀ a, c.X a ⟶ X) (h : Z ⟶ Y)
    (hf : ∀ a, f a ≫ i = c.f a ≫ h) :
    glueThroughMonoCut i c f h hf ≫ i = h := by
  apply c.hom_ext
  intro a
  rw [← Category.assoc]
  exact (congrArg (fun z => z ≫ i)
    (c.ι_glueMorphisms f (glueThroughMono_compatibleCut i c f h hf) a)).trans (hf a)

private def isoFromMonoProjectionsCut
    {X Y S T : Scheme.{u}} (e : X ≅ Y)
    (q : S ⟶ X) (p : T ⟶ Y) [Mono q] [Mono p]
    (f : S ⟶ T) (g : T ⟶ S)
    (hf : f ≫ p = q ≫ e.hom) (hg : g ≫ q = p ≫ e.inv) : S ≅ T where
  hom := f
  inv := g
  hom_inv_id := by
    apply (cancel_mono q).mp
    calc
      (f ≫ g) ≫ q = f ≫ (p ≫ e.inv) := by rw [Category.assoc, hg]
      _ = (q ≫ e.hom) ≫ e.inv := by rw [← Category.assoc, hf]
      _ = (𝟙 S) ≫ q := by simp
  inv_hom_id := by
    apply (cancel_mono p).mp
    calc
      (g ≫ f) ≫ p = g ≫ (q ≫ e.hom) := by rw [Category.assoc, hf]
      _ = (p ≫ e.inv) ≫ e.hom := by rw [← Category.assoc, hg]
      _ = (𝟙 T) ≫ p := by simp

private theorem invertNativeChartProjectionCut
    {U V S T X Y : Scheme.{u}} (a : U ≅ V) (e : X ≅ Y)
    (i : U ⟶ S) (j : V ⟶ T) (q : S ⟶ X) (p : T ⟶ Y)
    (h : a.hom ≫ j ≫ p = i ≫ q ≫ e.hom) :
    a.inv ≫ i ≫ q = j ≫ p ≫ e.inv := by
  have hh := congrArg (fun z => a.inv ≫ z ≫ e.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh.symm

private theorem backwardCompositeProjectionCut
    {W U V S T Y : Scheme.{u}}
    (r : W ⟶ V) (a : V ⟶ U) (i : U ⟶ S) (q : S ⟶ Y)
    (j : V ⟶ T) (p : T ⟶ Y) (k : W ⟶ T)
    (hi : a ≫ i ≫ q = j ≫ p) (hr : r ≫ j = k) :
    (r ≫ a ≫ i) ≫ q = k ≫ p := by
  calc
    (r ≫ a ≫ i) ≫ q = r ≫ (a ≫ i ≫ q) := by simp only [Category.assoc]
    _ = r ≫ (j ≫ p) := congrArg (fun z => r ≫ z) hi
    _ = (r ≫ j) ≫ p := (Category.assoc r j p).symm
    _ = k ≫ p := congrArg (fun z => z ≫ p) hr

private theorem standardNativeParametrization_inverseIsoHomCut :
    standardProjectiveLineToTwistedCubic (K := K) =
      (standardTwistedCubicProjectiveLineIso (K := K)).symm.hom := rfl

private abbrev chosenStandardIntersectionIdeal
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :=
  I ⊔ equationIdeal
    (linearSubstitution ((Classical.choose hB : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) F)
    (linearSubstitution_homogeneous _ hF)

private abbrev chosenBinaryEquationIdeal
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :=
  equationIdeal (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K)
    (hB.literalRestrictedBinaryNine F hF).property

private def chosenStandardIntersectionCurveMap
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (chosenStandardIntersectionIdeal hB F hF) ⟶ scheme I :=
  schemeQuotientMap I _ (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)

private def chosenBinaryEquationLineMap
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (chosenBinaryEquationIdeal hB F hF) ⟶ scheme L :=
  schemeQuotientMap L _ (by exact bot_le)

private instance chosenStandardIntersectionCurveMap_closedImmersion
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    IsClosedImmersion (chosenStandardIntersectionCurveMap hB F hF) :=
  schemeQuotientMap_closedImmersion _ _ _

private instance chosenBinaryEquationLineMap_closedImmersion
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    IsClosedImmersion (chosenBinaryEquationLineMap hB F hF) :=
  schemeQuotientMap_closedImmersion _ _ _

private theorem nativeChartMorphism_curveFactorizationCut (b : Bool) :
    standardTwistedCubicNativeChartMorphism (K := K) b ≫
      chartι I (if b then 3 else 0) =
        chartι L b ≫ standardProjectiveLineToTwistedCubic (K := K) := by
  cases b
  · exact (standardProjectiveLineChartZero_toTwistedCubic (K := K)).symm
  · exact (standardProjectiveLineChartThree_toTwistedCubic (K := K)).symm

private def binaryNineLocalForward
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool) :
    Spec (.of (ChartRing (chosenBinaryEquationIdeal hB F hF) b)) ⟶
      scheme (chosenStandardIntersectionIdeal hB F hF) :=
  (hB.literalBinaryNineNativeChartIso F hF b).hom ≫
    chartι (chosenStandardIntersectionIdeal hB F hF) (if b then 3 else 0)

private theorem binaryNineLocalForward_projection
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool) :
    binaryNineLocalForward hB F hF b ≫ chosenStandardIntersectionCurveMap hB F hF =
      chartι (chosenBinaryEquationIdeal hB F hF) b ≫
        (chosenBinaryEquationLineMap hB F hF ≫
          standardProjectiveLineToTwistedCubic (K := K)) := by
  change ((hB.literalBinaryNineNativeChartIso F hF b).hom ≫
    chartι (chosenStandardIntersectionIdeal hB F hF) (if b then 3 else 0)) ≫
      schemeQuotientMap I _ _ = _
  rw [Category.assoc, chartι_schemeQuotientMap, ← Category.assoc,
    hB.literalBinaryNineNativeChartIso_projection, Category.assoc,
    nativeChartMorphism_curveFactorizationCut, ← Category.assoc,
    ← chartι_schemeQuotientMap]
  exact Category.assoc (chartι (chosenBinaryEquationIdeal hB F hF) b)
    (chosenBinaryEquationLineMap hB F hF) (standardProjectiveLineToTwistedCubic (K := K))

private def binaryNineLocalBackward
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool) :
    pullback (chosenStandardIntersectionCurveMap hB F hF)
      (chartι I (if b then 3 else 0)) ⟶ scheme (chosenBinaryEquationIdeal hB F hF) :=
  (isPullback_schemeQuotientMap_chart I (chosenStandardIntersectionIdeal hB F hF)
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)
    (if b then 3 else 0)).flip.isoPullback.inv ≫
      (hB.literalBinaryNineNativeChartIso F hF b).inv ≫
        chartι (chosenBinaryEquationIdeal hB F hF) b

private theorem binaryNineLocalBackward_projection
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (b : Bool) :
    binaryNineLocalBackward hB F hF b ≫ chosenBinaryEquationLineMap hB F hF =
      pullback.fst (chosenStandardIntersectionCurveMap hB F hF)
        (chartι I (if b then 3 else 0)) ≫
          (chosenStandardIntersectionCurveMap hB F hF ≫
            (standardTwistedCubicProjectiveLineIso (K := K)).hom) := by
  let c := (isPullback_schemeQuotientMap_chart I (chosenStandardIntersectionIdeal hB F hF)
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)
    (if b then 3 else 0)).flip
  let a := hB.literalBinaryNineNativeChartIso F hF b
  have hp := binaryNineLocalForward_projection hB F hF b
  have hp' : a.inv ≫ chartι (chosenBinaryEquationIdeal hB F hF) b ≫
      chosenBinaryEquationLineMap hB F hF =
      chartι (chosenStandardIntersectionIdeal hB F hF) (if b then 3 else 0) ≫
        chosenStandardIntersectionCurveMap hB F hF ≫
          (standardTwistedCubicProjectiveLineIso (K := K)).hom := by
    exact invertNativeChartProjectionCut a
      (standardTwistedCubicProjectiveLineIso (K := K)).symm
      (chartι (chosenBinaryEquationIdeal hB F hF) b)
      (chartι (chosenStandardIntersectionIdeal hB F hF) (if b then 3 else 0))
      (chosenBinaryEquationLineMap hB F hF)
      (chosenStandardIntersectionCurveMap hB F hF)
      (by simpa only [binaryNineLocalForward, a, Category.assoc,
        standardNativeParametrization_inverseIsoHomCut] using hp)
  exact backwardCompositeProjectionCut c.isoPullback.inv a.inv
    (chartι (chosenBinaryEquationIdeal hB F hF) b) (chosenBinaryEquationLineMap hB F hF)
    (chartι (chosenStandardIntersectionIdeal hB F hF) (if b then 3 else 0))
    (chosenStandardIntersectionCurveMap hB F hF ≫
      (standardTwistedCubicProjectiveLineIso (K := K)).hom)
    (pullback.fst (chosenStandardIntersectionCurveMap hB F hF)
      (chartι I (if b then 3 else 0))) hp' c.isoPullback_inv_fst

private def binaryNineGlobalForward
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (chosenBinaryEquationIdeal hB F hF) ⟶
      scheme (chosenStandardIntersectionIdeal hB F hF) :=
  glueThroughMonoCut (chosenStandardIntersectionCurveMap hB F hF)
    (coordinateOpenCover (chosenBinaryEquationIdeal hB F hF)).openCover
    (binaryNineLocalForward hB F hF)
    (chosenBinaryEquationLineMap hB F hF ≫ standardProjectiveLineToTwistedCubic (K := K))
    (binaryNineLocalForward_projection hB F hF)

private theorem binaryNineGlobalForward_projection
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    binaryNineGlobalForward hB F hF ≫ chosenStandardIntersectionCurveMap hB F hF =
      chosenBinaryEquationLineMap hB F hF ≫ standardProjectiveLineToTwistedCubic (K := K) :=
  glueThroughMonoCut_projection _ _ _ _ _

private def binaryNineGlobalBackward
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (chosenStandardIntersectionIdeal hB F hF) ⟶
      scheme (chosenBinaryEquationIdeal hB F hF) :=
  glueThroughMonoCut (chosenBinaryEquationLineMap hB F hF)
    ((standardTwistedCubicOpenCover (K := K)).pullback₁
      (chosenStandardIntersectionCurveMap hB F hF))
    (binaryNineLocalBackward hB F hF)
    (chosenStandardIntersectionCurveMap hB F hF ≫
      (standardTwistedCubicProjectiveLineIso (K := K)).hom)
    (binaryNineLocalBackward_projection hB F hF)

private theorem binaryNineGlobalBackward_projection
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    binaryNineGlobalBackward hB F hF ≫ chosenBinaryEquationLineMap hB F hF =
      chosenStandardIntersectionCurveMap hB F hF ≫
        (standardTwistedCubicProjectiveLineIso (K := K)).hom :=
  glueThroughMonoCut_projection _ _ _ _ _

/-- Global binary hypersurface is Iso to the WHOLE original transformed
intersection. The two inverse maps are glued from the actual chart Isos,
with compatibility DERIVED by their original curve/line projections. -/
def GroundTwistedCubicPresentation.literalBinaryNineNativeGlobalIso
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (chosenBinaryEquationIdeal hB F hF) ≅
      scheme (chosenStandardIntersectionIdeal hB F hF) :=
  isoFromMonoProjectionsCut (standardTwistedCubicProjectiveLineIso (K := K)).symm
    (chosenBinaryEquationLineMap hB F hF) (chosenStandardIntersectionCurveMap hB F hF)
    (binaryNineGlobalForward hB F hF) (binaryNineGlobalBackward hB F hF)
    (binaryNineGlobalForward_projection hB F hF) (binaryNineGlobalBackward_projection hB F hF)

/-- The global scheme Iso has EXACTLY the SAME original line-to-curve
projection. The equation restriction is not a support-only identification. -/
theorem GroundTwistedCubicPresentation.literalBinaryNineNativeGlobalIso_projection
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    (hB.literalBinaryNineNativeGlobalIso F hF).hom ≫
        chosenStandardIntersectionCurveMap hB F hF =
      chosenBinaryEquationLineMap hB F hF ≫
        standardProjectiveLineToTwistedCubic (K := K) := by
  exact binaryNineGlobalForward_projection hB F hF

/-- The literal binary hypersurface is the ORIGINAL ground WHOLE
intersection scheme. Both coordinate transports use EXACTLY the matrix
already selected by the original ground parametrization. -/
def GroundTwistedCubicPresentation.literalBinaryNineOriginalWholeIntersectionIso
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    scheme (equationIdeal (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K)
      (hB.literalRestrictedBinaryNine F hF).property) ≅
        scheme (groundTwistedCubicCubicIntersectionIdeal B F hF) := by
  let A : GL (Fin 4) K := Classical.choose hB
  have hdet : IsUnit ((A : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)
  have hIJ : (chosenStandardIntersectionIdeal hB F hF).toIdeal =
      (groundTwistedCubicCubicIntersectionIdeal B F hF).toIdeal.map
        (linearSubstitutionEquiv (A : Matrix (Fin 4) (Fin 4) K) hdet).toRingHom :=
    groundTwistedCubicCubicIntersectionIdeal_coordinate_map B A
      (Classical.choose_spec hB) F hF hdet
  exact hB.literalBinaryNineNativeGlobalIso F hF ≪≫
    (linearCoordinateChangeSchemeIso (A : Matrix (Fin 4) (Fin 4) K) hdet
      (groundTwistedCubicCubicIntersectionIdeal B F hF)
      (chosenStandardIntersectionIdeal hB F hF) hIJ).symm

end PfaffianDescent.QuarticNet
