import PfaffianDescent.OriginalNormalizedPolynomialGlobalHilbertChartIso
import PfaffianDescent.RelativeClosedAmbientTestMap313

/-! Exact original-base ambient maps behind the normalized312/chosen-chart
classifier comparison. The physical coefficient chart and entire ideals are
retained; no Cartesian square, ambient iso or map equality is a caller input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
/-- Small projection comparison before any original coordinate subtype is
substituted. This checks only native pullback projections and actual maps. -/
private theorem originalNormalizedAmbientOpenSquare_from_projections001
    {X B U Y Z : Scheme.{u}} (F : X ⟶ B) (i : U ⟶ X) (T : Over B)
    (e : Y ⟶ pullback T.hom (i ≫ F)) (f : Z ⟶ pullback T.hom F) (a : Y ⟶ Z)
    (hTest : e ≫ relativeHilbertFamily197 (i ≫ F) T =
      (a ≫ f) ≫ relativeHilbertFamily197 F T)
    (hOriginal : (e ≫ pullback.snd T.hom (i ≫ F)) ≫ i =
      (a ≫ f) ≫ pullback.snd T.hom F) :
    e ≫ relativeClosedAmbientTestMap313 i F T = a ≫ f := by
  apply pullback.hom_ext
  · exact (Category.assoc e (relativeClosedAmbientTestMap313 i F T) _).trans
      ((congrArg (fun g => e ≫ g) (relativeClosedAmbientTestMap_toTest313 i F T)).trans hTest)
  · exact (Category.assoc e (relativeClosedAmbientTestMap313 i F T) _).trans
      ((congrArg (fun g => e ≫ g) (relativeClosedAmbientTestMap_toOriginal313 i F T)).trans
        ((Category.assoc e (pullback.snd T.hom (i ≫ F)) i).symm.trans hOriginal))

variable {R : Type u} [CommRing R]
variable (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4)

/-- Exact scalar map of the SAME original coordinate basic open. -/
def originalNormalizedCoordinateOpenFamily001 :=
  (Proj.basicOpen (grading (equationIdeal p hp))
    (originalNormalizedCoordinateChartIndex001 p hp j).val).ι ≫ toBase (equationIdeal p hp)

/-- Cartesian square of the actual normalized-to-basic-open comparison,
on every original-base test. -/
theorem originalNormalizedPolynomialBasicOpen_relativeCartesian001
    (T : Over (Spec (.of R))) :
    IsPullback
      (pullback.snd T.hom (originalNormalizedPolynomialFamily317 R p j) ≫
        (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom)
      (relativeHilbertFamily197 (originalNormalizedPolynomialFamily317 R p j) T)
      (originalNormalizedCoordinateOpenFamily001 p hp j) T.hom := by
  have hRight : IsPullback (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom
      (originalNormalizedPolynomialFamily317 R p j)
      (originalNormalizedCoordinateOpenFamily001 p hp j) (𝟙 (Spec (.of R))) :=
    IsPullback.of_horiz_isIso_mono ⟨by
      have hBase : (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom ≫
          originalNormalizedCoordinateOpenFamily001 p hp j =
            originalNormalizedPolynomialFamily317 R p j := by
        change (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom ≫
          ((Proj.basicOpen (grading (equationIdeal p hp))
            (originalNormalizedCoordinateChartIndex001 p hp j).val).ι ≫
              toBase (equationIdeal p hp)) = _
        exact originalNormalizedPolynomialBasicOpenIso_overBase001 p hp j
      exact hBase.trans (Category.comp_id _).symm⟩
  simpa only [relativeHilbertFamily197, Category.comp_id] using
    (IsPullback.of_hasPullback T.hom (originalNormalizedPolynomialFamily317 R p j)).flip.paste_horiz hRight

/-- Actual relative ambient iso underlying the already constructed all-test
functor comparison; its source is the literal normalized polynomial ambient. -/
def originalNormalizedPolynomialBasicOpenRelativeAmbientIso001
    (T : Over (Spec (.of R))) :
    pullback T.hom (originalNormalizedPolynomialFamily317 R p j) ≅
      pullback T.hom (originalNormalizedCoordinateOpenFamily001 p hp j) :=
  nativeRelativeCartesianChartIso317 (originalNormalizedCoordinateOpenFamily001 p hp j) T
    (pullback.snd T.hom (originalNormalizedPolynomialFamily317 R p j) ≫
      (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom)
    (relativeHilbertFamily197 (originalNormalizedPolynomialFamily317 R p j) T)
    (originalNormalizedPolynomialBasicOpen_relativeCartesian001 p hp j T)

theorem originalNormalizedPolynomialBasicOpenRelativeAmbientIso_toTest001
    (T : Over (Spec (.of R))) :
    (originalNormalizedPolynomialBasicOpenRelativeAmbientIso001 p hp j T).hom ≫
      relativeHilbertFamily197 (originalNormalizedCoordinateOpenFamily001 p hp j) T =
        relativeHilbertFamily197 (originalNormalizedPolynomialFamily317 R p j) T :=
  nativeRelativeCartesianChartIso_toTest317 _ _ _ _ _

theorem originalNormalizedPolynomialBasicOpenRelativeAmbientIso_toChart001
    (T : Over (Spec (.of R))) :
    (originalNormalizedPolynomialBasicOpenRelativeAmbientIso001 p hp j T).hom ≫
      pullback.snd T.hom (originalNormalizedCoordinateOpenFamily001 p hp j) =
        pullback.snd T.hom (originalNormalizedPolynomialFamily317 R p j) ≫
          (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom :=
  nativeRelativeCartesianChartIso_toOriginal317 _ _ _ _ _

/-- Exact WHOLE-ideal dictionary for the previously constructed functor,
with its actual native ambient iso now public. -/
theorem originalNormalizedPolynomialBasicOpenHilbertFunctorIso_wholeIdeal001
    (T : Over (Spec (.of R))) (n : ℕ)
    (Q : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (originalNormalizedPolynomialFamily317 R p j) T) n) :
    ((originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n).hom.app (.op T) Q).val =
      Q.val.comap (originalNormalizedPolynomialBasicOpenRelativeAmbientIso001 p hp j T).inv := by
  rfl

variable (B : Type u) [CommRing B] [Algebra R B]

/-- The physical normalized coefficient chart, with its actual composite
Cartesian iso into the SAME original coordinate-open relative ambient. -/
def originalNormalizedPolynomialPhysicalBasicOpenAmbientIso001 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)) ≅
      pullback (originalNormalizedAffineTest317 R B).hom
        (originalNormalizedCoordinateOpenFamily001 p hp j) :=
  originalNormalizedAffineTestAmbientIso317 R p hp j B ≪≫
    originalNormalizedPolynomialBasicOpenRelativeAmbientIso001 p hp j
      (originalNormalizedAffineTest317 R B)

theorem originalNormalizedPolynomialPhysicalBasicOpenAmbientIso_toTest001 :
    (originalNormalizedPolynomialPhysicalBasicOpenAmbientIso001 p hp j B).hom ≫
      relativeHilbertFamily197 (originalNormalizedCoordinateOpenFamily001 p hp j)
        (originalNormalizedAffineTest317 R B) =
      Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j))) := by
  exact (Category.assoc
    (originalNormalizedAffineTestAmbientIso317 R p hp j B).hom
    (originalNormalizedPolynomialBasicOpenRelativeAmbientIso001 p hp j
      (originalNormalizedAffineTest317 R B)).hom
    (relativeHilbertFamily197 (originalNormalizedCoordinateOpenFamily001 p hp j)
      (originalNormalizedAffineTest317 R B))).trans
    ((congrArg (fun f => (originalNormalizedAffineTestAmbientIso317 R p hp j B).hom ≫ f)
      (originalNormalizedPolynomialBasicOpenRelativeAmbientIso_toTest001 p hp j
        (originalNormalizedAffineTest317 R B))).trans
      (originalNormalizedAffineTestAmbientIso_toTest317 R p hp j B))

theorem originalNormalizedPolynomialPhysicalBasicOpenAmbientIso_toChart001 :
    (originalNormalizedPolynomialPhysicalBasicOpenAmbientIso001 p hp j B).hom ≫
      pullback.snd (originalNormalizedAffineTest317 R B).hom
        (originalNormalizedCoordinateOpenFamily001 p hp j) =
      originalNormalizedProjectiveChartReduction312 (algebraMap R B) p hp j ≫
        (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom := by
  have hNorm : (originalNormalizedAffineTestAmbientIso317 R p hp j B).hom ≫
      pullback.snd (originalNormalizedAffineTest317 R B).hom
        (originalNormalizedPolynomialFamily317 R p j) =
      originalNormalizedProjectiveChartReduction312 (algebraMap R B) p hp j :=
    (originalNormalizedAffineTest_isPullback317 R p hp j B).flip.isoPullback_hom_snd
  exact (Category.assoc
    (originalNormalizedAffineTestAmbientIso317 R p hp j B).hom
    (originalNormalizedPolynomialBasicOpenRelativeAmbientIso001 p hp j
      (originalNormalizedAffineTest317 R B)).hom _).trans
    ((congrArg (fun f => (originalNormalizedAffineTestAmbientIso317 R p hp j B).hom ≫ f)
      (originalNormalizedPolynomialBasicOpenRelativeAmbientIso_toChart001 p hp j
        (originalNormalizedAffineTest317 R B))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom) hNorm)))

/-- Both constructed ambient transports retain the entire physical ideal. -/
theorem originalNormalizedPolynomialPhysicalBasicOpenAmbientIso_wholeIdeal001
    (n : ℕ) (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    ((originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n).hom.app
      (.op (originalNormalizedAffineTest317 R B))
        (originalNormalizedAffineTestPointEquiv317 R p hp j B n Q)).val =
      Q.val.comap (originalNormalizedPolynomialPhysicalBasicOpenAmbientIso001 p hp j B).inv := by
  exact (originalNormalizedPolynomialBasicOpenHilbertFunctorIso_wholeIdeal001 p hp j
    (originalNormalizedAffineTest317 R B) n
    (originalNormalizedAffineTestPointEquiv317 R p hp j B n Q)).trans
    ((congrArg (fun I => I.comap
      (originalNormalizedPolynomialBasicOpenRelativeAmbientIso001 p hp j
        (originalNormalizedAffineTest317 R B)).inv)
      (originalNormalizedAffineTestPointEquiv_wholeIdeal317 R p hp j B n Q)).trans
      (Q.val.comap_comp
        (originalNormalizedPolynomialBasicOpenRelativeAmbientIso001 p hp j
          (originalNormalizedAffineTest317 R B)).inv
        (originalNormalizedAffineTestAmbientIso317 R p hp j B).inv).symm)

/-- Physical original projective coefficient pullback, retaining its original
Spec B and original polynomial coefficient map. -/
def originalNormalizedPolynomialPhysicalProjectiveAmbientIso001 :
    hypersurface (p.map (algebraMap R B)) (hp.map (algebraMap R B)) ≅
      pullback (originalNormalizedAffineTest317 R B).hom (hypersurfaceToBase p hp) :=
  nativeRelativeCartesianChartIso317 (hypersurfaceToBase p hp) (originalNormalizedAffineTest317 R B)
    (hypersurfaceReductionMap (algebraMap R B) p hp (p.map (algebraMap R B))
      (hp.map (algebraMap R B)) rfl)
    (hypersurfaceToBase (p.map (algebraMap R B)) (hp.map (algebraMap R B)))
    (isPullback_hypersurfaceReductionMap (algebraMap R B) p hp
      (p.map (algebraMap R B)) (hp.map (algebraMap R B)) rfl)

/-- The actual ambient square needed for WHOLE-ideal push/comap. It compares
maps, not just supports: normalized physical embedding followed by the
original projective Cartesian iso is the actual coordinate-open test map. -/
theorem originalNormalizedPolynomialPhysicalBasicOpenAmbientIso_toProjective001 :
    (originalNormalizedPolynomialPhysicalBasicOpenAmbientIso001 p hp j B).hom ≫
      relativeClosedAmbientTestMap313
        (Proj.basicOpen (grading (equationIdeal p hp))
          (originalNormalizedCoordinateChartIndex001 p hp j).val).ι
        (hypersurfaceToBase p hp) (originalNormalizedAffineTest317 R B) =
      originalNormalizedHypersurfaceChartEmbedding312 (p.map (algebraMap R B))
        (hp.map (algebraMap R B)) j ≫
          (originalNormalizedPolynomialPhysicalProjectiveAmbientIso001 p hp B).hom := by
  let T := originalNormalizedAffineTest317 R B
  let F := hypersurfaceToBase p hp
  let i := (Proj.basicOpen (grading (equationIdeal p hp))
    (originalNormalizedCoordinateChartIndex001 p hp j).val).ι
  let e := originalNormalizedPolynomialPhysicalBasicOpenAmbientIso001 p hp j B
  let f := originalNormalizedPolynomialPhysicalProjectiveAmbientIso001 p hp B
  let a := originalNormalizedHypersurfaceChartEmbedding312 (p.map (algebraMap R B))
    (hp.map (algebraMap R B)) j
  let c := hypersurfaceReductionMap (algebraMap R B) p hp (p.map (algebraMap R B))
    (hp.map (algebraMap R B)) rfl
  let fB := hypersurfaceToBase (p.map (algebraMap R B)) (hp.map (algebraMap R B))
  let y := Spec.map (CommRingCat.ofHom (R := B)
    (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
    (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))
  have hPTest : f.hom ≫ relativeHilbertFamily197 F T = fB :=
    nativeRelativeCartesianChartIso_toTest317 F T c fB
      (isPullback_hypersurfaceReductionMap (algebraMap R B) p hp
        (p.map (algebraMap R B)) (hp.map (algebraMap R B)) rfl)
  have hPOriginal : f.hom ≫ pullback.snd T.hom F = c :=
    nativeRelativeCartesianChartIso_toOriginal317 F T c fB
      (isPullback_hypersurfaceReductionMap (algebraMap R B) p hp
        (p.map (algebraMap R B)) (hp.map (algebraMap R B)) rfl)
  have hTestL : e.hom ≫ relativeHilbertFamily197 (i ≫ F) T = y :=
    originalNormalizedPolynomialPhysicalBasicOpenAmbientIso_toTest001 p hp j B
  have hTestR : (a ≫ f.hom) ≫ relativeHilbertFamily197 F T = y :=
    (Category.assoc a f.hom _).trans
      ((congrArg (fun g => a ≫ g) hPTest).trans
        (originalNormalizedHypersurfaceChartEmbedding_toBase312
          (p.map (algebraMap R B)) (hp.map (algebraMap R B)) j))
  have hOriginalR : (a ≫ f.hom) ≫ pullback.snd T.hom F = a ≫ c :=
    (Category.assoc a f.hom _).trans (congrArg (fun g => a ≫ g) hPOriginal)
  have hChart : e.hom ≫ pullback.snd T.hom (i ≫ F) =
      originalNormalizedProjectiveChartReduction312 (algebraMap R B) p hp j ≫
        (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom :=
    originalNormalizedPolynomialPhysicalBasicOpenAmbientIso_toChart001 p hp j B
  have hOriginalL : (e.hom ≫ pullback.snd T.hom (i ≫ F)) ≫ i = a ≫ c :=
    (congrArg (fun g => g ≫ i) hChart).trans
      ((Category.assoc _ _ i).trans
        ((congrArg (fun g =>
          originalNormalizedProjectiveChartReduction312 (algebraMap R B) p hp j ≫ g)
          (originalNormalizedPolynomialBasicOpenIso_embedding001 p hp j)).trans
          (originalNormalizedProjectiveChartReduction_toOriginal312 (algebraMap R B) p hp j)))
  exact originalNormalizedAmbientOpenSquare_from_projections001 F i T e.hom f.hom a
    (hTestL.trans hTestR.symm) (hOriginalL.trans hOriginalR.symm)

end PfaffianDescent
end
