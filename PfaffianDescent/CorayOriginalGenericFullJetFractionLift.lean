import PfaffianDescent.CorayOriginalNativeFullJetHyperplaneDictionary
import PfaffianDescent.CorayOriginalGenericDifferentialDimensionAndSmoothImage
import Mathlib.RingTheory.Localization.FractionRing

/-! The literal generic chart fulljet extends to ORIGINAL F. Every
coefficient, residue and normalized coordinate value is preserved.
No tangent rank/determinant/open certificate is supplied. SOURCE ONLY / HELD. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A genuine chart fulljet with the actual fraction-field residue map
extends uniquely by localization; its whole-field residue is identity. -/
theorem fractionFieldFullJet_exists_lift
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (J : A →+* SurfacePlaneJet F)
    (hfst : ∀ a, (J a).fst = algebraMap A F a) :
    ∃ ell : F →+* SurfacePlaneJet F,
      ell.comp (algebraMap A F) = J ∧ ∀ z, (ell z).fst = z := by
  have hunit : ∀ a : nonZeroDivisors A, IsUnit (J a.1) := by
    intro a
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    rw [hfst]
    exact IsLocalization.map_units F a
  let ell : F →+* SurfacePlaneJet F := IsLocalization.lift (M := nonZeroDivisors A) hunit
  have hcomp : ell.comp (algebraMap A F) = J := IsLocalization.lift_comp hunit
  have hresidue : (TrivSqZeroExt.fstHom F F (Fin 2 → F)).toRingHom.comp ell = RingHom.id F := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors A)
    ext a
    change (ell (algebraMap A F a)).fst = algebraMap A F a
    rw [IsLocalization.lift_eq, hfst]
  exact ⟨ell, hcomp, fun z => RingHom.congr_fun hresidue z⟩

/-- The original normalized coordinate is sent to its entire prescribed
fulljet value; this derives the required residue comparison internally. -/
theorem cubicNormalizedFullJetChartMap_coordinate001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (j : Fin 4) (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1) (i : Fin 4) :
    cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      (chartCoordinate (equationIdeal p hp) j i) = surfacePlaneJetCoordinates z v i := by
  let I := equationIdeal p hp
  let qEval : CoordinateRing I →+* SurfacePlaneJet M :=
    (cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ).toRingHom
  have hOne : qEval (coordinate I j) = 1 := by
    change MvPolynomial.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) (X j) = 1
    simpa only [eval₂_X] using hAnchor
  change (AllCharacteristics.GradedChart.liftCoordinateOne (grading I) (coordinate I j)
    qEval hOne) (AllCharacteristics.GradedChart.normalized (grading I)
      (coordinate_mem I j) (coordinate I i) (coordinate_mem I i)) = _
  rw [AllCharacteristics.GradedChart.liftCoordinateOne_normalized]
  change MvPolynomial.eval₂ (algebraMap K (SurfacePlaneJet M))
    (surfacePlaneJetCoordinates z v) (X i) = _
  exact MvPolynomial.eval₂_X _ _ i

/-- Literal chart generation compares the fulljet residue with the
actual chart field point, including the independent original K square. -/
theorem cubicNormalizedFullJetChartMap_fst_eq001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v j = 1) :
    ∀ r : ChartRing (equationIdeal p hp) j,
      (cubicNormalizedFullJetChartMap p hp j
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v hpJ hAnchor r).fst = g r := by
  let z : Fin 4 → M := fun i => g (chartCoordinate (equationIdeal p hp) j i)
  let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  let rho : ChartRing (equationIdeal p hp) j →+* M :=
    (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom.comp J
  have heq : rho = g := by
    ext r
    obtain ⟨q, rfl⟩ := eval₂_chartCoordinate_surjective (equationIdeal p hp) j r
    change rho (q.eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j)) =
      g (q.eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j))
    rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂]
    have hcoeff : rho.comp (chartBaseMap (equationIdeal p hp) j) =
        g.comp (chartBaseMap (equationIdeal p hp) j) := by
      ext c
      change (J (chartBaseMap (equationIdeal p hp) j c)).fst = g (chartBaseMap (equationIdeal p hp) j c)
      rw [cubicNormalizedFullJetChartMap_base001]
      change algebraMap K M c = g (chartBaseMap (equationIdeal p hp) j c)
      have hc : g (chartBaseMap (equationIdeal p hp) j c) = algebraMap K M c :=
        RingHom.congr_fun hBase c
      exact hc.symm
    have hcoords : (fun i => rho (chartCoordinate (equationIdeal p hp) j i)) =
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) := by
      funext i
      change (J (chartCoordinate (equationIdeal p hp) j i)).fst = g (chartCoordinate (equationIdeal p hp) j i)
      rw [cubicNormalizedFullJetChartMap_coordinate001]
      simp only [surfacePlaneJetCoordinates, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, z]
    rw [hcoeff, hcoords]
  intro r
  exact RingHom.congr_fun heq r

/-- ORIGINAL smoothness constructs the actual generic fulljet field map,
with identity residue, the original coefficient hom and the actual
Jacobian-pivot coordinate directions all as conclusions. -/
theorem smoothOriginalCubic_generic_exists_nativeFieldJet001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let g := @affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j) (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
    let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
    ∃ pivot : Fin 3,
      MvPolynomial.aeval z (pderiv (j.succAbove pivot) (p.map (algebraMap K F))) ≠ 0 ∧
      ∃ ell : F →+* SurfacePlaneJet F,
      (∀ x, (ell x).fst = x) ∧
      (∀ c : K, ell (algebraMap K F c) = TrivSqZeroExt.inl (algebraMap K F c)) ∧
      (∀ i : Fin 4, ell (z i) = surfacePlaneJetCoordinates z
        (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
          (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i r) i) := by
  let A := ChartRing (equationIdeal p hp) j
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let g : A →+* F := @affineChartGenericEvaluation A (inferInstance : CommRing A)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  have hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K F :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  obtain ⟨hpz, pivot, hpivot, hpJ, hAnchor⟩ :=
    smoothOriginalCubic_chartFieldPoint_exists_nativeFullJet001 p hp hp0 j g hBase
  let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
  let v : Fin 2 → Fin 4 → F := fun r i =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i r
  let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  letI : Algebra A F := g.toAlgebra
  letI : IsFractionRing A F := @affineChartGenericEvaluation_isFractionRing A
    (inferInstance : CommRing A) (hypersurface p hp)
    (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  obtain ⟨ell, hcomp, hfst⟩ := fractionFieldFullJet_exists_lift J
    (cubicNormalizedFullJetChartMap_fst_eq001 p hp j g hBase v hpJ hAnchor)
  have hgrad : MvPolynomial.aeval z
      (pderiv (j.succAbove pivot) (p.map (algebraMap K F))) ≠ 0 := by
    simpa only [MvPolynomial.pderiv_map, MvPolynomial.aeval_eq_eval,
      MvPolynomial.eval_map] using hpivot
  refine ⟨pivot, hgrad, ell, hfst, ?_, ?_⟩
  · intro c
    have hc := RingHom.congr_fun hBase c
    change g (chartBaseMap (equationIdeal p hp) j c) = algebraMap K F c at hc
    calc
      ell (algebraMap K F c) = ell (g (chartBaseMap (equationIdeal p hp) j c)) := congrArg ell hc.symm
      _ = J (chartBaseMap (equationIdeal p hp) j c) := RingHom.congr_fun hcomp _
      _ = algebraMap K (SurfacePlaneJet F) c := cubicNormalizedFullJetChartMap_base001 p hp j z v hpJ hAnchor c
      _ = TrivSqZeroExt.inl (algebraMap K F c) := rfl
  · intro i
    change ell (g (chartCoordinate (equationIdeal p hp) j i)) = _
    rw [show ell (g (chartCoordinate (equationIdeal p hp) j i)) =
      J (chartCoordinate (equationIdeal p hp) j i) from RingHom.congr_fun hcomp _]
    exact cubicNormalizedFullJetChartMap_coordinate001 p hp j z v hpJ hAnchor i

end PfaffianDescent.Coray
end
