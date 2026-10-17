import PfaffianDescent.OriginalClosedPointGlobalHilbertSmoothClassifierLift
import PfaffianDescent.ProjectiveGlobalUniversalOriginalPointRecovery
import PfaffianDescent.OriginalGlobalHilbertCoefficientFieldRecovery

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u v w
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Reassociate only the actual classifier's three maps, before original
polynomial families and the dependent global parameter are substituted. -/
private theorem originalGlobalClassifierComposition_reassociate001
    {C : Type v} [Category.{w} C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) :
    a ≫ (b ≫ c) = (a ≫ b) ≫ c := (Category.assoc a b c).symm

variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
  (hr : r.IsHomogeneous 3) (K : Type u) [Field K] [Algebra R K]
  (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
local notation "pointDegree" => Scheme.Hom.residueDegree
  (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))) P.val
local notation "pointPositive" => originalClosedPoint_residueDegree_pos317 R r hr K P

/-- The complete-local ORIGINAL cubic receives the physical pullback of the
ACTUAL glued global universal family. Its exact original-P fibre is derived
from the chosen-chart classifier and whole-ideal recovery. No local317
lifted-family producer, selected classifier or fibre outcome is an input. -/
theorem originalClosedPoint_globalHilbertFiniteFlatClosedSubscheme001
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ hypersurface r hr)
      (u0 : Spec ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).residueField P.val) ⟶ Z),
      IsClosedImmersion a ∧ IsFinite (a ≫ hypersurfaceToBase r hr) ∧
      Flat (a ≫ hypersurfaceToBase r hr) ∧
      (∀ y, (a ≫ hypersurfaceToBase r hr).finrank y = pointDegree) ∧
      IsPullback u0
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val)
        a (hypersurfaceReductionMap (algebraMap R K) r hr
          (r.map (algebraMap R K)) (hr.map (algebraMap R K)) rfl) := by
  obtain ⟨j, i, k, hk, hPoint, hSmooth, cLocal, cGlobal, hGlobal, hLocalReduction, hGlobalReduction⟩ :=
    originalClosedPoint_globalHilbertSmoothClassifierLift_completeAlgebra001
      R r hr K P hK0 hRK (Algebra.ofId R K) hRK
  letI : IsSeparated (hypersurfaceToBase r hr) := originalNormalizedWholeOpen_separated317 r hr
  let F := hypersurfaceToBase r hr
  let U := fun a : projectivePositiveHomogeneousChartIndex001 (grading (equationIdeal r hr)) =>
    Proj.basicOpen (grading (equationIdeal r hr)) a.val
  let H := originalPositiveHomogeneousChartIndexRepresentingObject001
    (equationIdeal r hr) pointDegree pointPositive
  let eta := originalPositiveHomogeneousChartIndexRepresentingIso001
    (equationIdeal r hr) pointDegree pointPositive
  let T0 := originalNormalizedAffineTest317 R K
  let T1 := originalNormalizedAffineTest317 R R
  let b := originalNormalizedAffineTestMap317 R (Algebra.ofId R K)
  let d := hypersurfaceReductionMap (algebraMap R K) r hr
    (r.map (algebraMap R K)) (hr.map (algebraMap R K)) rfl
  let F0 := hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))
  have h0 : IsPullback d F0 F T0.hom :=
    isPullback_hypersurfaceReductionMap (algebraMap R K) r hr
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) rfl
  have hSelf : T1.hom = 𝟙 (Spec (.of R)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap R R)) = _
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have h1 : IsPullback (𝟙 (hypersurface r hr)) F F T1.hom := by
    rw [hSelf]
    exact IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp, Category.comp_id]⟩
  let g0 := originalCoefficientTestClassifyingMap317 R 3 pointDegree
    (originalNormalizedHypersurfacePolynomial312 r j) i k ≫
      (originalNormalizedPolynomialChosenChartOverIso001 r hr j pointDegree pointPositive).hom
  have hReduction : b ≫ cGlobal = g0 ≫
      relativeOpenChartParameterGluedChartInclusionOver001 F U pointDegree H eta
        (originalNormalizedCoordinateChartIndex001 r hr j) := by
    have hChart : originalCoefficientTestGlobalClassifyingMap001 r hr j pointDegree pointPositive i k =
        g0 ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U pointDegree H eta
          (originalNormalizedCoordinateChartIndex001 r hr j) :=
      originalGlobalClassifierComposition_reassociate001
        (originalCoefficientTestClassifyingMap317 R 3 pointDegree
          (originalNormalizedHypersurfacePolynomial312 r j) i k)
        (originalNormalizedPolynomialChosenChartOverIso001 r hr j pointDegree pointPositive).hom
        (relativeOpenChartParameterGluedChartInclusionOver001 F U pointDegree H eta
          (originalNormalizedCoordinateChartIndex001 r hr j))
    exact hGlobalReduction.trans hChart
  have ha : d ≫ 𝟙 (hypersurface r hr) = d := Category.comp_id d
  have hf : d ≫ F = F0 ≫ b.left :=
    hypersurfaceReductionMap_toBase (algebraMap R K) r hr
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) rfl
  have hSeed :
      (relativeOpenChartClassifiedAmbientPoint001 F (U (originalNormalizedCoordinateChartIndex001 r hr j))
        pointDegree (H (originalNormalizedCoordinateChartIndex001 r hr j))
        (eta (originalNormalizedCoordinateChartIndex001 r hr j)) T0 g0).val.comap
          (nativeRelativeCartesianChartIso317 F T0 d F0 h0).hom =
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker := by
    exact (originalCoefficientChosenChart_physicalWholeIdeal001 R r hr j K pointDegree pointPositive i k).trans hPoint
  let Q := relativeOpenChartGlobalUniversalPhysicalFamily001 F U pointDegree H eta
    T1 (𝟙 (hypersurface r hr)) F h1 cGlobal
  obtain ⟨u0, hCartesian⟩ :=
    relativeOpenChartGlobalUniversalPhysicalFamily_originalPoint_isPullback001
      F U pointDegree H eta b d F0 h0 (𝟙 (hypersurface r hr)) F h1 d ha hf
      cGlobal (originalNormalizedCoordinateChartIndex001 r hr j) g0 hReduction P hSeed
  exact ⟨Q.val.subscheme, Q.val.subschemeι, u0,
    inferInstance, Q.property.1, Q.property.2.1, Q.property.2.2, hCartesian⟩

end PfaffianDescent
end
