import PfaffianDescent.AffineTraceSelectedQuotientAndJet
import PfaffianDescent.QuarticActualChartAffineGradient
import PfaffianDescent.ActualNativeChartNormalizedAlgebraPoint

/- SOURCE ONLY / UNVERIFIED. Keep the actual AFFINE trace-selected q and
its v while reversing the TRUE original chart permutation. The native
ring-map residue and ALL homogeneous quadratic trace values are derived.
This is an auxiliary fixed-chart theorem; the original-P caller derives
its chart and basis rather than taking coordinate certificates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actualFixedNativeChart_exists_retainedAffineTraceJet
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* L)
    (hbase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K L)
    (b : Basis (Fin 4) K L)
    (hb : ∀ a, b a = g (chartCoordinate (equationIdeal p hp) j a)) :
    let I := equationIdeal p hp
    let sigma := Equiv.swap (0 : Fin 4) j
    let b' := b.reindex sigma
    let c := fun a : Fin 3 => b' a.succ
    let F := QuarticNet.dehomogenizeAtZero (rename sigma p)
    let T := LinearMap.ker (QuarticNet.affineDifferential c F)
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    ∃ q : Module.Dual L T →ₗ[L] L,
      Function.Surjective q ∧
      (Algebra.trace K L).comp ((q.restrictScalars K).comp
        (QuarticNet.affineQuadricCotangentRestriction c F)) = 0 ∧
      ∃ phi : ChartRing I j →ₐ[K] DualNumber L,
        Function.Surjective phi ∧
        (∀ r, (phi r).fst = g r) ∧
        (∀ Q : MvPolynomial (Fin 4) K, Q.IsHomogeneous 2 →
          g (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0 →
          Algebra.trace K L ((phi (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j))).snd) = 0) ∧
        (∀ Q : QuarticNet.affineQuadricsThroughPoint (k := K) c,
          (phi ((rename sigma.symm (QuarticNet.homogeneousAffineQuadrics Q.val)).eval₂
            (chartBaseMap I j) (chartCoordinate I j))).snd =
              q (QuarticNet.affineQuadricCotangentRestriction c F Q)) := by
  classical
  dsimp only
  let I := equationIdeal p hp
  letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  let sigma := Equiv.swap (0 : Fin 4) j
  let b' := b.reindex sigma
  let c : Fin 3 → L := fun a => b' a.succ
  let F := QuarticNet.dehomogenizeAtZero (rename sigma p)
  let T := LinearMap.ker (QuarticNet.affineDifferential c F)
  have hbj : b j = 1 := by rw [hb, chartCoordinate_self, map_one]
  have hb0 : b' 0 = 1 := by simpa [b', sigma] using hbj
  have hdiff : QuarticNet.affineDifferential c F ≠ 0 := by
    simpa [c, F, b', sigma] using
      smoothCubic_actualChart_swapped_affineDifferential_ne_zero p hp hp0 j g hbase b hb
  have hpB : aeval b p = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p
      (Ideal.subset_span (Set.mem_singleton p)))
    rw [hom_eval₂, hbase, map_zero] at h
    rw [show (b : Fin 4 → L) = (fun a => g (chartCoordinate I j a)) from funext hb,
      aeval_def]
    simpa only [Function.comp_def] using h
  have hbcomp : (fun a => b' (sigma a)) = b := by
    funext a
    simp [b', sigma]
  have hpoint : aeval c F = 0 := by
    rw [show F = QuarticNet.dehomogenizeAtZero (rename sigma p) from rfl,
      QuarticNet.aeval_dehomogenizeAtZero _ b' hb0, aeval_rename]
    change aeval (fun a => b' (sigma a)) p = 0
    rw [hbcomp]
    exact hpB
  obtain ⟨q, hq, htrace, hv, hkernel, hquad, hjetQ⟩ :=
    QuarticNet.good_affine_tangent_direction_with_trace_quotient b' hb0 F hdiff
  let v : T := (Module.evalEquiv L T).symm q
  have hvVal : v.val ≠ 0 := by intro h; exact hv (Subtype.ext h)
  have hjet : QuarticNet.affineFirstJet c v.val F = 0 :=
    (QuarticNet.affineFirstJet_eq_zero_iff c v.val F).mpr ⟨hpoint, v.property⟩
  let y' := QuarticNet.homogeneousAffineDualPoint c v.val
  let y : Fin 4 → DualNumber L := y' ∘ sigma.symm
  have hy : y j = 1 := by simp [y, y', sigma, QuarticNet.homogeneousAffineDualPoint]
  have hyComp : y ∘ sigma = y' := by funext a; simp [y]
  have hySymm : y ∘ sigma.symm = y' := by funext a; simp [y, sigma]
  have hfst (a : Fin 4) : (y' a).fst = b' a := by
    fin_cases a <;> simp [y', QuarticNet.homogeneousAffineDualPoint, c, hb0]
  have hredY (a : Fin 4) : (y a).fst = g (chartCoordinate I j a) := by
    change (y' (sigma.symm a)).fst = _
    rw [hfst]
    simpa [b', sigma] using hb a
  have heP : aeval y p = 0 := by
    rw [QuarticNet.affineFirstJet_dehomogenize] at hjet
    have hperm : rename sigma.symm (rename sigma p) = p := by
      rw [rename_rename, sigma.symm_comp_self, rename_id_apply]
    rw [← hperm, aeval_rename]
    simpa [Function.comp_def, y, sigma] using hjet
  have he : ∀ Q ∈ I.toIdeal, Q.eval₂ (algebraMap K (DualNumber L)) y = 0 := by
    have hle : I.toIdeal ≤ RingHom.ker (aeval y).toRingHom := by
      apply Ideal.span_le.mpr
      rintro Q hQ
      obtain rfl := Set.mem_singleton_iff.mp hQ
      exact heP
    exact fun Q hQ => hle hQ
  have hgen : Function.Surjective (eval₂Hom (algebraMap K (DualNumber L)) y) := by
    intro z
    obtain ⟨Q, hQ⟩ := QuarticNet.homogeneousAffineDualPoint_eval_surjective c v.val
      (QuarticNet.affineResidueEvaluation_surjective b' hb0) hvVal z
    refine ⟨rename sigma Q, ?_⟩
    change aeval y (rename sigma Q) = z
    rw [aeval_rename, hyComp]
    exact hQ
  obtain ⟨psi, hcoords, hPoint⟩ := exists_coordinateChartMap_eq_linearNormalizedPoint
    I y (X j) (isHomogeneous_X K j) (by simpa only [eval₂_X] using hy) he j 1 hy.symm
  have hpsiBase : psi.comp (chartBaseMap I j) = algebraMap K (DualNumber L) := by
    have h := congrArg (fun t => t ≫ toBase I) hPoint
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp, linearNormalizedPoint_toBase] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  let phi : ChartRing I j →ₐ[K] DualNumber L :=
    { psi with commutes' := fun a => RingHom.congr_fun hpsiBase a }
  have hEval (Q : MvPolynomial (Fin 4) K) :
      phi (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = aeval y Q := by
    change psi (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = _
    rw [hom_eval₂, hpsiBase]
    congr 1
    funext a
    simpa using hcoords a
  have hphi : Function.Surjective phi := by
    intro z
    obtain ⟨Q, hQ⟩ := hgen z
    refine ⟨Q.eval₂ (chartBaseMap I j) (chartCoordinate I j), ?_⟩
    rw [hEval]
    exact hQ
  have hredPhi (r : ChartRing I j) : (phi r).fst = g r := by
    obtain ⟨Q, rfl⟩ := eval₂_chartCoordinate_surjective I j r
    change (phi (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j))).fst =
      g (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [hEval, hom_eval₂, hbase]
    change (TrivSqZeroExt.fstHom K L L).toRingHom (Q.eval₂ (algebraMap K (DualNumber L)) y) = _
    have hfBase : (TrivSqZeroExt.fstHom K L L).toRingHom.comp
        (algebraMap K (DualNumber L)) = algebraMap K L := by
      ext c
      exact (TrivSqZeroExt.fstHom K L L).commutes c
    rw [hom_eval₂, hfBase]
    congr 1
    funext a
    exact hredY a
  have hPermEval (Q : MvPolynomial (Fin 4) K) :
      aeval y Q = aeval y' (rename sigma Q) := by
    rw [aeval_rename]
    congr 1
  have hCoefficient (Q : QuarticNet.affineQuadricsThroughPoint (k := K) c) :
      (phi ((rename sigma.symm (QuarticNet.homogeneousAffineQuadrics Q.val)).eval₂
        (chartBaseMap I j) (chartCoordinate I j))).snd =
      q (QuarticNet.affineQuadricCotangentRestriction c F Q) := by
    rw [hEval, aeval_rename, hySymm]

    rw [QuarticNet.homogeneousAffineQuadrics_eval_dual]
    exact hjetQ Q
  have hTraceAll (Q : MvPolynomial (Fin 4) K) (hQ : Q.IsHomogeneous 2)
      (hQ0 : g (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0) :
      Algebra.trace K L ((phi (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j))).snd) = 0 := by
    obtain ⟨a, ha⟩ := QuarticNet.homogeneousAffineQuadrics_exhaustive
      (rename sigma Q) hQ.rename_isHomogeneous
    have hEvalQ : phi (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
        QuarticNet.affineFirstJet c v.val (QuarticNet.affineQuadrics a) := by
      rw [hEval, hPermEval, ← ha, QuarticNet.homogeneousAffineQuadrics_eval_dual]
    have ha0 : a ∈ QuarticNet.affineQuadricsThroughPoint (k := K) c := by
      change aeval c (QuarticNet.affineQuadrics a) = 0
      have h := (hredPhi (Q.eval₂ (chartBaseMap I j) (chartCoordinate I j))).trans hQ0
      rw [hEvalQ] at h
      simpa only [QuarticNet.affineFirstJet_fst] using h
    let a0 : QuarticNet.affineQuadricsThroughPoint (k := K) c := ⟨a, ha0⟩
    have ht := congrArg (fun m => m a0) htrace
    change Algebra.trace K L (q (QuarticNet.affineQuadricCotangentRestriction c F a0)) = 0 at ht
    rw [hEvalQ, hjetQ a0]
    exact ht
  exact ⟨q, hq, htrace, phi, hphi, hredPhi, hTraceAll, hCoefficient⟩

end PfaffianDescent
