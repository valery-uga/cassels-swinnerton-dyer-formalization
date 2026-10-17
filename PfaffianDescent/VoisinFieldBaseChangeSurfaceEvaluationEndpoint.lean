import PfaffianDescent.VoisinFieldBaseChangeDescentEndpoint
import PfaffianDescent.VoisinProjectiveChartPullbackCoordinates

/-!
# Fixed-linear-system descent from surface-chart basis values

The endpoint can be supplied with geometric evaluations computed on the
underlying surface charts. The comparison with the normalized
surface--parameter chart is proved in
`VoisinProjectiveChartPullbackCoordinates`.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open BundleSectionZeroLocus

universe u

noncomputable section

/-- Field-base-change endpoint expressed in terms of evaluated coordinates
of the original basis sections on affine surface charts. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_surfaceBasisEvaluation
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (s : SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := L) base)
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M))
    (hs : s ≠ 0)
    (hlocalSurfaceBasisEvaluation : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
          r ≫ marked i →
      ∀ a : I,
        ∃ geometricEvaluation :
            SchemeModuleGlobalSectionsOver
              (schemeFieldBaseChangeToField (L := L) base)
              ((Scheme.Modules.pullback
                (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
                →ₗ[L] L,
          (∀ k : Fin (Module.finrank K
              (SchemeModuleGlobalSectionsOver base M)),
            geometricEvaluation
                ((schemeModuleGlobalSectionsOverEquivSections
                  (schemeFieldBaseChangeToField (L := L) base)
                  ((Scheme.Modules.pullback
                    (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm
                    (pullbackSection
                      (schemeFieldBaseChangeToOriginal (L := L) base) M
                      (isIso_pullbackUnitComparison
                        (schemeFieldBaseChangeToOriginal (L := L) base))
                      (schemeModuleGlobalSectionsOverEquivSections base M
                        (Module.finBasis K
                          (SchemeModuleGlobalSectionsOver base M) k)))) =
              C.projectiveSectionSurfaceBasisCoordinateEvaluation
                base M ij ri a k) ∧
          geometricEvaluation s = 0) :
    False := by
  apply C.no_generic_projectiveSection_fieldMember_of_pullbackBasisEvaluation
    base M
    (schemeFieldBaseChangeToField (L := L) base)
    (schemeFieldBaseChangeToOriginal (L := L) base)
    qBase n marked hmarked havoid r hr hrBase
    (C.globalSectionsFieldBaseChangeLinearMap_bijective
      (L := L) base M) s hs
  intro i ij ri hri a
  obtain ⟨geometricEvaluation, hbasis, hzero⟩ :=
    hlocalSurfaceBasisEvaluation i ij ri hri a
  refine ⟨geometricEvaluation, ?_, hzero⟩
  intro k
  rw [C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap_finBasis_eq_surface
    base M ij ri a k]
  exact hbasis k

end

end PfaffianDescent
