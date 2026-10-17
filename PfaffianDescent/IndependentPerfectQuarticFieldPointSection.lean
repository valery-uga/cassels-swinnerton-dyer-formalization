import PfaffianDescent.PerfectFieldQuarticPointChartBasis
import PfaffianDescent.QuarticActualChartAffineGradient
import PfaffianDescent.QuarticExceptionalGroundJetSection
import PfaffianDescent.IndependentHypersurfaceSectionRenameTransport

/- SOURCE ONLY / UNVERIFIED. Exact actual quartic field point frontend
for the independent affine tangent-net argument. Residue basis, chart-zero
normalization and nonzero affine differential are derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem independent_perfectField_actualQuarticPoint_rational_section
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (h4 : finrank K L = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp) i) :
    ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  classical
  obtain ⟨j, g, hbase, hpoint, b, hb, hbj⟩ :=
    perfectField_quartic_fieldPoint_exists_actual_chart_basis
      (equationIdeal p hp) i hi h4 hspan
  let σ := Equiv.swap (0 : Fin 4) j
  let b' := b.reindex σ
  have hb0 : b' 0 = 1 := by simpa [b', σ] using hbj
  have hdiff : QuarticNet.affineDifferential (fun a : Fin 3 => b' a.succ)
      (QuarticNet.dehomogenizeAtZero (rename σ p)) ≠ 0 := by
    simpa [b', σ] using
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
  have hpF : aeval b' (rename σ p) = 0 := by
    rw [aeval_rename]
    change aeval (fun a => b' (σ a)) p = 0
    rw [hbcomp]
    exact hpB
  have hrenamed : ∃ s : Spec (.of K) ⟶ hypersurface (rename σ p) hp.rename_isHomogeneous,
      s ≫ hypersurfaceToBase (rename σ p) hp.rename_isHomogeneous = 𝟙 _ :=
    QuarticNet.cubic_section_of_smooth_affine_degree_four_point
      (K := AlgebraicClosure K) b' hb0 (rename σ p) hp.rename_isHomogeneous hpF hdiff
  exact independent_hypersurface_section_of_rename_section p hp σ hrenamed

end PfaffianDescent
