import PfaffianDescent.AffineTraceSelectedJetKaehlerComparison

/- SOURCE ONLY / UNVERIFIED. The same retained trace-selected q, actual
jet algebra and genuine Kaehler line are constructed together. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial Module
open scoped TensorProduct
universe u

theorem exists_traceSelected_actual_hypersurface_kaehler_quotient
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (b : Basis (Fin 4) K L) (hb : b 0 = 1) (F : AffineThreeRing K)
    (hpoint : MvPolynomial.aeval (fun i : Fin 3 => b i.succ) F = 0)
    (hF : affineDifferential (fun i : Fin 3 => b i.succ) F ≠ 0) :
    let p := fun i : Fin 3 => b i.succ
    let T := LinearMap.ker (affineDifferential p F)
    let phiQuadric := affineQuadricCotangentRestriction p F
    ∃ q : Module.Dual L T →ₗ[L] L,
      Function.Surjective q ∧
      (Algebra.trace K L).comp ((q.restrictScalars K).comp phiQuadric) = 0 ∧
      let R := AffineThreeRing K ⧸ Ideal.span {F}
      let phi := affineTraceQuotientHypersurfaceJet b F hpoint q
      let rho := actualDualQuotientResidue phi
      letI : Algebra R L := rho.toRingHom.toAlgebra
      letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
        (fun c => (rho.commutes c).symm)
      Function.Surjective phi ∧
      Function.Surjective (actualDualMorphismDifferentialFiberLine phi) ∧
      3 ≤ finrank K (LinearMap.ker ((q.restrictScalars K).comp phiQuadric)) ∧
      ∀ Q : affineQuadricsThroughPoint (k := K) p,
        actualDualMorphismDifferentialFiberLine phi
          ((1 : L) ⊗ₜ[R] KaehlerDifferential.D K R
            (Ideal.Quotient.mk (Ideal.span {F}) (affineQuadrics Q.val))) = q (phiQuadric Q) := by
  obtain ⟨q, hq, htrace, hv, hdim, hquad, hjet⟩ :=
    good_affine_tangent_direction_with_trace_quotient b hb F hF
  have hphi := affineTraceQuotientHypersurfaceJet_surjective b F hpoint hb q hq
  exact ⟨q, hq, htrace, hphi, actualDualMorphismDifferentialFiberLine_surjective _ hphi,
    hdim, affineTraceQuotientHypersurfaceJet_kaehler_quadric b F hpoint q⟩

end PfaffianDescent.QuarticNet
