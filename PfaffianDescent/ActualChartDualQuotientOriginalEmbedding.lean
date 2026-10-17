import PfaffianDescent.ActualChartNormalizedPointReduction
import PfaffianDescent.DualNumberPointSupport
import PfaffianDescent.QuarticGeometricSplitting
import PfaffianDescent.QuarticHomogeneousJets

/- SOURCE ONLY / UNVERIFIED. Generic actual chart-quotient embedding adapter.
Its conditional ring-map inputs are discharged by every Kaehler line below;
no map/closedness/rank certificate is a final universal-line premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Every ACTUAL surjective dual quotient of a chart embeds in the SAME
projective scheme with exact residue reduction, support and ground rank eight. -/
theorem actualChart_dualQuotient_original_embedding
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (i : Spec (.of L) ⟶ scheme I) (j : Fin 4)
    (g : ChartRing I j →+* L)
    (hbase : g.comp (chartBaseMap I j) = algebraMap K L)
    (hpoint : Spec.map (CommRingCat.ofHom g) ≫ chartι I j = i)
    (h4 : finrank K L = 4)
    (phi : letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
      ChartRing I j →ₐ[K] DualNumber L)
    (hphi : Function.Surjective phi)
    (hred : letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
      (TrivSqZeroExt.fstHom K L L).toRingHom.comp phi.toRingHom = g) :
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    ∃ q : Spec (.of (DualNumber L)) ⟶ scheme I,
      q = Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ chartι I j ∧
      IsClosedImmersion q ∧
      q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber L))) ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom L L L).toRingHom) ≫ q = i ∧
      Set.range q = Set.range i ∧
      ∃ hfinite : IsFinite (q ≫ toBase I),
        @AllCharacteristics.finiteSchemeRank K _ _ (q ≫ toBase I) hfinite = 8 ∧
        (∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
          Nonempty (pullback
            (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
            (q ≫ toBase I) ≅
            ∐ fun _ : J => Spec (.of (DualNumber (AlgebraicClosure K))))) := by
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  let y : Fin 4 → DualNumber L := fun a => phi (chartCoordinate I j a)
  have hphibase : phi.toRingHom.comp (chartBaseMap I j) =
      algebraMap K (DualNumber L) := by
    apply RingHom.ext
    intro c
    exact phi.commutes c
  have heval : eval₂Hom (algebraMap K (DualNumber L)) y =
      phi.toRingHom.comp (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
    apply RingHom.ext
    intro r
    rw [RingHom.comp_apply]
    change r.eval₂ (algebraMap K (DualNumber L)) y = phi (r.eval₂ _ _)
    have h := (hom_eval₂ r (chartBaseMap I j) phi.toRingHom (chartCoordinate I j)).symm
    rw [hphibase] at h
    simpa only [y, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  have he : ∀ r ∈ I.toIdeal, r.eval₂ (algebraMap K (DualNumber L)) y = 0 := by
    intro r hr
    change eval₂Hom (algebraMap K (DualNumber L)) y r = 0
    rw [heval, RingHom.comp_apply]
    exact (congrArg phi (eval₂_chartCoordinate_eq_zero_of_mem I j r hr)).trans (map_zero phi)
  have hy : y j = 1 := by
    rw [show y j = phi (chartCoordinate I j j) from rfl, chartCoordinate_self, map_one]
  have hgen : Function.Surjective (eval₂Hom (algebraMap K (DualNumber L)) y) := by
    rw [heval]
    exact hphi.comp (eval₂_chartCoordinate_surjective I j)
  let hz : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K (DualNumber L)) y) he) (coordinate I j) = 1 := by
    change (eval₂Hom (algebraMap K (DualNumber L)) y) (X j) = 1
    exact (eval₂Hom_X' _ _ _).trans hy
  let q := linearNormalizedPointAt I y he (coordinate I j) (coordinate_mem I j) hz
  have hq : IsClosedImmersion q := linearNormalizedPointAt_isClosedImmersion
    I y he (coordinate I j) (coordinate_mem I j) hz hgen
  have hqbase : q ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber L))) :=
    linearNormalizedPointAt_toBase I y he (coordinate I j) (coordinate_mem I j) hz
  have hchart : phi.toRingHom = linearNormalizedPointChartMapAt
      I y he (coordinate I j) (coordinate_mem I j) hz :=
    linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
      I y he (coordinate I j) (coordinate_mem I j) hz phi.toRingHom hphibase
      (by intro a; rfl)
  have hqchart : q = Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ chartι I j := by
    change Spec.map (CommRingCat.ofHom (linearNormalizedPointChartMapAt
      I y he (coordinate I j) (coordinate_mem I j) hz)) ≫ chartι I j = _
    rw [← hchart]
  have hredy : ∀ a, (TrivSqZeroExt.fstHom K L L) (y a) = g (chartCoordinate I j a) := by
    intro a
    exact RingHom.congr_fun hred (chartCoordinate I j a)
  have hfac : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom L L L).toRingHom) ≫ q = i :=
    actualChart_normalizedPoint_reduction I i j g hbase hpoint
      y he hy (TrivSqZeroExt.fstHom K L L) hredy
  have hrange : Set.range q = Set.range i := dualNumber_point_range_eq_residue_range i q hfac
  letI : IsFinite (q ≫ toBase I) := by
    rw [hqbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hlength : AllCharacteristics.finiteSchemeRank (q ≫ toBase I) = 8 := by
    rw [QuarticNet.dualNumberProjectivePoint_finiteSchemeRank I q hqbase]
    change finrank K (L × L) = 8
    simp [Module.finrank_prod, h4]
  obtain ⟨J, hJ, hcard, ⟨e⟩⟩ :=
    QuarticNet.degree_four_dualPoint_scheme_splits K (AlgebraicClosure K) L h4
  letI := hJ
  let e' := pullback.congrHom
    (rfl : Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) = _)
    hqbase
  exact ⟨q, hqchart, hq, hqbase, hfac, hrange, inferInstance,
    hlength, ⟨J, hJ, hcard, ⟨e' ≪≫ e⟩⟩⟩

end PfaffianDescent
