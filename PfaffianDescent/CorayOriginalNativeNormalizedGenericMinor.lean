import PfaffianDescent.CorayOriginalNativeNormalizedDerivationJetDictionary
import PfaffianDescent.CorayOriginalBasisRatioFieldNativeGenericMinor

/-! The actual SAME basis projection's normalized native fulljet has a
nonzero generic two-row minor, constructed from original smoothness and
the exact SAME Etrdeg2 branch. No rank/minor/jet/open premise is supplied.
SOURCE ONLY / HELD. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any genuine original-K derivation of an actual cubic chart field
point constructs the cubic fulljet relation and its normalized anchor.
The original cubic relation is derived from the chart quotient. -/
theorem derivationCubicChart_fulljet_relation_anchor001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* F)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K F)
    (d : Derivation K F (Fin 2 → F)) :
    let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
    let v : Fin 2 → Fin 4 → F := fun r i => d (z i) r
    p.eval₂ (algebraMap K (SurfacePlaneJet F)) (surfacePlaneJetCoordinates z v) = 0 ∧
      surfacePlaneJetCoordinates z v j = 1 := by
  let I := equationIdeal p hp
  let z : Fin 4 → F := fun i => g (chartCoordinate I j i)
  let v : Fin 2 → Fin 4 → F := fun r i => d (z i) r
  let ell := derivationFieldFullJet d
  have hcoordinates : (fun i => ell (z i)) = surfacePlaneJetCoordinates z v := by
    funext i
    apply TrivSqZeroExt.ext
    · change z i = (surfacePlaneJetCoordinates z v i).fst
      simp only [surfacePlaneJetCoordinates, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · change d (z i) = (surfacePlaneJetCoordinates z v i).snd
      simp only [surfacePlaneJetCoordinates, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, v]
  have hpI : p ∈ I.toIdeal := Ideal.subset_span (Set.mem_singleton p)
  have hpz : p.eval₂ (algebraMap K F) z = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hpI)
    rw [hom_eval₂, hBase, map_zero] at h
    exact h
  have hcoeff : ell.comp (algebraMap K F) = algebraMap K (SurfacePlaneJet F) := by
    apply RingHom.ext
    intro c
    exact derivationFieldFullJet_base001 d c
  constructor
  · rw [← hcoordinates]
    have h := congrArg ell hpz
    rw [hom_eval₂, hcoeff, map_zero] at h
    exact h
  · have hz : z j = 1 := by
      change g (chartCoordinate I j j) = 1
      rw [chartCoordinate_self, map_one]
    rw [← hcoordinates]
    change ell (z j) = 1
    rw [hz, map_one]

/-- A literal native fulljet restriction identifies each target chart
row with the derivative of the literal normalized original coordinate. -/
theorem nativeNormalizedFullJet_derivation_coordinate001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* F)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K F)
    (d : Derivation K F (Fin 2 → F))
    (v : Fin 2 → Fin 4 → F)
    (hd : ∀ i, d (g (chartCoordinate (equationIdeal p hp) j i)) = fun r => v r i)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet F))
      (surfacePlaneJetCoordinates (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v j = 1)
    {m : ℕ} (x : Fin m → ChartRing (equationIdeal p hp) j) (a : Fin m)
    (ha : g (x a) ≠ 0) (i : Fin m) :
    let J := cubicNormalizedFullJetChartMap p hp j
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v hpJ hAnchor
    let hUnit : IsUnit (J (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
      (by rw [cubicNormalizedFullJetChartMap_fst_eq001 p hp j g hBase v hpJ hAnchor];
          exact isUnit_iff_ne_zero.mpr ha)
    let mu : Localization.Away (x a) →+* SurfacePlaneJet F := IsLocalization.Away.lift (x a) hUnit
    (mu (nativeLocalizedProjectiveChartMap (chartBaseMap (equationIdeal p hp) j) x a
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i))).snd =
      d (g (x i) / g (x a)) := by
  let J := cubicNormalizedFullJetChartMap p hp j
    (fun i => g (chartCoordinate (equationIdeal p hp) j i)) v hpJ hAnchor
  have hJ : (derivationFieldFullJet d).comp g = J :=
    derivationFieldFullJet_comp_chart_eq_nativeFullJet001 p hp j g hBase d v hd hpJ hAnchor
  let hUnit : IsUnit (J (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    (by rw [cubicNormalizedFullJetChartMap_fst_eq001 p hp j g hBase v hpJ hAnchor];
        exact isUnit_iff_ne_zero.mpr ha)
  let mu : Localization.Away (x a) →+* SurfacePlaneJet F := IsLocalization.Away.lift (x a) hUnit
  let hUnitD : IsUnit (((derivationFieldFullJet d).comp g) (x a)) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr ha)
  let muD : Localization.Away (x a) →+* SurfacePlaneJet F := IsLocalization.Away.lift (x a) hUnitD
  have hmu : mu = muD := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (x a))
    rw [IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    exact hJ.symm
  change (mu _).snd = _
  rw [hmu]
  exact nativeLocalizedProjectiveChartMap_fulljet_snd_eq_normalizedDerivation001
    (chartBaseMap (equationIdeal p hp) j) x a g ha d i

/-- ORIGINAL smoothness and the actual SAME Etrdeg2 branch construct a
native pivot jet and an actual nonzero minor of its normalized SAME
basis projection chart rows. Coefficients, denominator and map are exact. -/
theorem cubicThroughPointBasis_exists_nativeNormalizedGeneric_minor_of_trdeg_two001
    {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m) :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let g := @affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j) (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
    let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
    let x : Fin m → ChartRing (equationIdeal p hp) j := fun i =>
      cubicThroughPointChartEvaluation p hp n y hpy j (b i)
    Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 →
    ∃ pivot : Fin 3,
      MvPolynomial.aeval z (pderiv (j.succAbove pivot) (p.map (algebraMap K F))) ≠ 0 ∧
      let v : Fin 2 → Fin 4 → F := fun r i =>
        PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
          (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i r
      ∃ hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet F)) (surfacePlaneJetCoordinates z v) = 0,
      ∃ hAnchor : surfacePlaneJetCoordinates z v j = 1,
      let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      ∃ hUnit : IsUnit (J (x a)),
      let mu : Localization.Away (x a) →+* SurfacePlaneJet F := IsLocalization.Away.lift (x a) hUnit
      let row : Fin m → Fin 2 → F := fun i =>
        (mu (nativeLocalizedProjectiveChartMap (chartBaseMap (equationIdeal p hp) j) x a
          (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i))).snd
      ∃ i k : Fin m, row i 0 * row k 1 - row i 1 * row k 0 ≠ 0 := by
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let g := @affineChartGenericEvaluation
    (ChartRing (equationIdeal p hp) j) (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j) (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  let z : Fin 4 → F := fun i => g (chartCoordinate (equationIdeal p hp) j i)
  let x : Fin m → ChartRing (equationIdeal p hp) j := fun i =>
    cubicThroughPointChartEvaluation p hp n y hpy j (b i)
  change Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 → _
  intro hE
  obtain ⟨pivot, hgrad, d, hbij, hd, i, k, hminor⟩ :=
    cubicThroughPointOriginalBasisRatioField_exists_nativeGeneric_minor_of_trdeg_two001
      p hp hp0 n y hpy j b a hE
  let v : Fin 2 → Fin 4 → F := fun r i =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i r
  have hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K F :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  have hv : (fun r i => d (z i) r) = v := by
    funext r t
    exact congrFun (hd t) r
  obtain ⟨hpJ, hAnchor⟩ := derivationCubicChart_fulljet_relation_anchor001 p hp j g hBase d
  rw [hv] at hpJ hAnchor
  let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  have ha : g (x a) ≠ 0 := cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a
  let hUnit : IsUnit (J (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    (by rw [cubicNormalizedFullJetChartMap_fst_eq001 p hp j g hBase v hpJ hAnchor];
        exact isUnit_iff_ne_zero.mpr ha)
  let mu : Localization.Away (x a) →+* SurfacePlaneJet F := IsLocalization.Away.lift (x a) hUnit
  have hrow (t : Fin m) :
      (mu (nativeLocalizedProjectiveChartMap (chartBaseMap (equationIdeal p hp) j) x a
        (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a t))).snd =
      d (g (x t) / g (x a)) :=
    nativeNormalizedFullJet_derivation_coordinate001 p hp j g hBase d v hd hpJ hAnchor x a ha t
  refine ⟨pivot, hgrad, hpJ, hAnchor, hUnit, i, k, ?_⟩
  change (mu _).snd 0 * (mu _).snd 1 - (mu _).snd 1 * (mu _).snd 0 ≠ 0
  rw [hrow i, hrow k]
  exact hminor

end PfaffianDescent.Coray
end
