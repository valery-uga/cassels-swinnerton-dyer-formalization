import PfaffianDescent.NormalizedPointIntrinsicQuadraticInclusion
import PfaffianDescent.PerfectFieldActualQuarticTangentJetCoordinates
import PfaffianDescent.ActualChartNormalizedPointReduction
import PfaffianDescent.DualNumberPointSupport
import PfaffianDescent.QuarticGeometricSplitting

/-! One actual ground tangent subscheme keeps the original degree-four
point as its exact support, has length eight, splits into four dual-number
points, and has a full quadratic system of dimension at least three. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem perfectField_actualQuarticPoint_exists_original_tangentSubscheme
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (h4 : finrank K L = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp) i) :
    letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
    ∃ (q : Spec (.of (DualNumber L)) ⟶ hypersurface p hp) (y : Fin 4 → DualNumber L),
      IsClosedImmersion q ∧
      q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber L))) ∧
      Set.range q = Set.range i ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom L L L).toRingHom) ≫ q = i ∧
      ∃ hfinite : IsFinite (q ≫ hypersurfaceToBase p hp),
        @AllCharacteristics.finiteSchemeRank K _ _ (q ≫ hypersurfaceToBase p hp) hfinite = 8 ∧
        (∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
          Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
            (q ≫ hypersurfaceToBase p hp) ≅
            ∐ fun _ : J => Spec (.of (DualNumber (AlgebraicClosure K))))) ∧
        3 ≤ finrank K (homogeneousVanishingPolynomialSubmodule (K := K) y 2) ∧
        3 ≤ finrank K (intrinsicFullQuadraticSystem (q ≫ quotientProjMap (equationIdeal p hp))) ∧
        ∃ (j : Fin 4)
          (he : ∀ r ∈ (equationIdeal p hp).toIdeal,
            r.eval₂ (algebraMap K (DualNumber L)) y = 0)
          (hz : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
            (eval₂Hom (algebraMap K (DualNumber L)) y) he)
            (coordinate (equationIdeal p hp) j) = 1),
          q = linearNormalizedPointAt (equationIdeal p hp) y he
            (coordinate (equationIdeal p hp) j) (coordinate_mem (equationIdeal p hp) j) hz := by
  classical
  letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  obtain ⟨j, g, hbase, hpoint, y, hy, he, hgen, hred, hquad⟩ :=
    perfectField_actualQuarticPoint_exists_tangentJet_coordinates p hp hp0 i hi h4 hspan
  let hz : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K (DualNumber L)) y) he)
      (coordinate (equationIdeal p hp) j) = 1 := by
    simpa only [coordinate, Ideal.Quotient.lift_mk, eval₂Hom_X'] using hy
  let q := linearNormalizedPointAt (equationIdeal p hp) y he
    (coordinate (equationIdeal p hp) j) (coordinate_mem (equationIdeal p hp) j) hz
  have hq : IsClosedImmersion q :=
    linearNormalizedPointAt_isClosedImmersion (equationIdeal p hp) y he
      (coordinate (equationIdeal p hp) j) (coordinate_mem (equationIdeal p hp) j) hz hgen
  have hqbase : q ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber L))) :=
    linearNormalizedPointAt_toBase (equationIdeal p hp) y he
      (coordinate (equationIdeal p hp) j) (coordinate_mem (equationIdeal p hp) j) hz
  have hfac : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom L L L).toRingHom) ≫ q = i :=
    actualChart_normalizedPoint_reduction (equationIdeal p hp) i j g hbase hpoint
      y he hy (TrivSqZeroExt.fstHom K L L) hred
  have hrange : Set.range q = Set.range i := dualNumber_point_range_eq_residue_range i q hfac
  letI : IsFinite (q ≫ hypersurfaceToBase p hp) := by
    rw [hqbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite (q ≫ toBase (equationIdeal p hp)) := by
    change IsFinite (q ≫ hypersurfaceToBase p hp)
    infer_instance
  have hlength : AllCharacteristics.finiteSchemeRank (q ≫ hypersurfaceToBase p hp) = 8 := by
    change AllCharacteristics.finiteSchemeRank (q ≫ toBase (equationIdeal p hp)) = 8
    rw [QuarticNet.dualNumberProjectivePoint_finiteSchemeRank (equationIdeal p hp) q hqbase]
    change finrank K (L × L) = 8
    simp [Module.finrank_prod, h4]
  have hIntrinsic : 3 ≤ finrank K
      (intrinsicFullQuadraticSystem (q ≫ quotientProjMap (equationIdeal p hp))) := by
    apply hquad.trans
    simpa only [q, normalizedFiniteEquationPoint, coordinate] using
      normalizedFiniteEquationPoint_intrinsicQuadrics_finrank_ge
        (equationIdeal p hp) y (X j) (isHomogeneous_X K j)
        (by simpa only [eval₂_X] using hy) he
  obtain ⟨J, hJ, hcard, ⟨e⟩⟩ :=
    QuarticNet.degree_four_dualPoint_scheme_splits K (AlgebraicClosure K) L h4
  letI := hJ
  let e' := pullback.congrHom
    (rfl : Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) = _)
    hqbase
  exact ⟨q, y, hq, hqbase, hrange, hfac, inferInstance, hlength,
    ⟨J, hJ, hcard, ⟨e' ≪≫ e⟩⟩, hquad, hIntrinsic, j, he, hz, rfl⟩

end PfaffianDescent
