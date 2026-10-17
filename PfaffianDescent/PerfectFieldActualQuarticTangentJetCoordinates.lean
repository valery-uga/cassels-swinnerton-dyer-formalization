import PfaffianDescent.PerfectFieldQuarticPointChartBasis
import PfaffianDescent.QuarticActualChartAffineGradient
import PfaffianDescent.QuarticActualJetFullQuadrics

/-! Construct one tangent jet in the ORIGINAL homogeneous coordinates of
an actual degree-four field point. The residue basis and nonzero differential
are derived from geometric spanning and smoothness. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_actualQuarticPoint_exists_tangentJet_coordinates
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (h4 : finrank K L = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp) i) :
    letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
    ∃ (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* L),
      g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K L ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j = i ∧
      ∃ y : Fin 4 → DualNumber L,
        y j = 1 ∧
        (∀ q ∈ (equationIdeal p hp).toIdeal, q.eval₂ (algebraMap K (DualNumber L)) y = 0) ∧
        Function.Surjective (eval₂Hom (algebraMap K (DualNumber L)) y) ∧
        (∀ a, (y a).fst = g (chartCoordinate (equationIdeal p hp) j a)) ∧
        3 ≤ finrank K (homogeneousVanishingPolynomialSubmodule (K := K) y 2) := by
  classical
  letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  obtain ⟨j, g, hbase, hpoint, b, hb, hbj⟩ :=
    perfectField_quartic_fieldPoint_exists_actual_chart_basis
      (equationIdeal p hp) i hi h4 hspan
  let σ := Equiv.swap (0 : Fin 4) j
  let b' := b.reindex σ
  have hb0 : b' 0 = 1 := by simpa [b', σ] using hbj
  let c : Fin 3 → L := fun a => b' a.succ
  let F := QuarticNet.dehomogenizeAtZero (rename σ p)
  have hdiff : QuarticNet.affineDifferential c F ≠ 0 := by
    simpa [c, F, b', σ] using
      smoothCubic_actualChart_swapped_affineDifferential_ne_zero p hp hp0 j g hbase b hb
  have hpB : aeval b p = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem
      (equationIdeal p hp) j p (Ideal.subset_span (Set.mem_singleton p)))
    rw [hom_eval₂, hbase, map_zero] at h
    change p.eval₂ (algebraMap K L) (fun a => b a) = 0
    rw [show (fun a => b a) =
      (fun a => g (chartCoordinate (equationIdeal p hp) j a)) from funext hb]
    simpa only [Function.comp_def] using h
  have hbcomp : (fun a => b' (σ a)) = b := by
    funext a
    simp [b', σ]
  have hpF : aeval c F = 0 := by
    rw [show F = QuarticNet.dehomogenizeAtZero (rename σ p) from rfl,
      QuarticNet.aeval_dehomogenizeAtZero _ b' hb0, aeval_rename]
    change aeval (fun a => b' (σ a)) p = 0
    rw [hbcomp]
    exact hpB
  obtain ⟨v, hv, ht, hdim⟩ := QuarticNet.good_affine_tangent_direction b' hb0 F hdiff
  have hjet : QuarticNet.affineFirstJet c v F = 0 :=
    (QuarticNet.affineFirstJet_eq_zero_iff c v F).mpr ⟨hpF, ht⟩
  let y' := QuarticNet.homogeneousAffineDualPoint c v
  let y : Fin 4 → DualNumber L := y' ∘ σ.symm
  have hy : y j = 1 := by simp [y, y', σ, QuarticNet.homogeneousAffineDualPoint]
  have hfst (a : Fin 4) : (y' a).fst = b' a := by
    fin_cases a <;> simp [y', QuarticNet.homogeneousAffineDualPoint, c, hb0]
  have hred (a : Fin 4) : (y a).fst = g (chartCoordinate (equationIdeal p hp) j a) := by
    change (y' (σ.symm a)).fst = _
    rw [hfst]
    simpa [b', σ] using hb a
  have hycomp : y ∘ σ = y' := by
    funext a
    simp [y]
  have heP : aeval y p = 0 := by
    rw [QuarticNet.affineFirstJet_dehomogenize] at hjet
    have hperm : (rename σ.symm (rename σ p)) = p := by
      rw [rename_rename, σ.symm_comp_self, rename_id_apply]
    rw [← hperm, aeval_rename]
    simpa [Function.comp_def, y, σ] using hjet
  have he : ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K (DualNumber L)) y = 0 := by
    have hle : (equationIdeal p hp).toIdeal ≤ RingHom.ker (aeval y).toRingHom := by
      change Ideal.span {p} ≤ _
      apply Ideal.span_le.mpr
      intro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      exact heP
    exact fun q hq => hle hq
  have hgen' : Function.Surjective (eval₂Hom (algebraMap K (DualNumber L)) y') :=
    QuarticNet.homogeneousAffineDualPoint_eval_surjective c v
      (QuarticNet.affineResidueEvaluation_surjective b' hb0) hv
  have hgen : Function.Surjective (eval₂Hom (algebraMap K (DualNumber L)) y) := by
    intro z
    obtain ⟨q, hq⟩ := hgen' z
    refine ⟨rename σ q, ?_⟩
    change aeval y (rename σ q) = z
    rw [aeval_rename, hycomp]
    exact hq
  exact ⟨j, g, hbase, hpoint, y, hy, he, hgen, hred,
    quartic_actualJet_fullQuadrics_finrank_ge_three c v σ hdim⟩

end PfaffianDescent
