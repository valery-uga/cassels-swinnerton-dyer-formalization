import PfaffianDescent.GroundTwistedCubicNativeCompleteBasis
import PfaffianDescent.CasselsOriginalPointNativeCubicCoordinateImages

/-! SOURCE ONLY. The actual unfinished original-P coordinate-image
consumer is strengthened to a COMPLETE native linear series. All original
point, containing curve, immersion and base/ambient squares are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable instance originalPointCompleteSeriesHZeroAddCommGroup
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (Q : X.Modules) :
    AddCommGroup (SchemeModuleGlobalSectionsOver p Q) :=
  instAddCommGroupSchemeModuleGlobalSectionsOver (K := K) (X := X) p Q

private noncomputable instance originalPointCompleteSeriesHZeroModule
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (Q : X.Modules) :
    Module K (SchemeModuleGlobalSectionsOver p Q) :=
  instModuleSchemeModuleGlobalSectionsOver (K := K) (X := X) p Q

set_option backward.isDefEq.respectTransparency.types false in
/-- ORIGINAL perfect-field degree4/5 nonplane P constructs its SAME
containing ground twisted cubic and ORIGINAL residue-field immersion. The
four ORIGINAL ambient coordinates form a basis of the GENUINE full native
H0 pullback, and retain the SAME literal cubic whole-map image identities.
No containing curve, image, basis, H0, bundle or completeness premise is input. -/
theorem perfectField_original_closedPoint_exists_twistedCubic_nativeCompleteSeries
    {K : Type u} [Field K] [PerfectField K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (P : closedPoints (hypersurface F hF))
    (hdim : (hypersurfaceToBase F hF).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase F hF).residueDegree P.1 = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal F hF).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal) :
    ∃ B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      ∃ hB : QuarticNet.GroundTwistedCubicPresentation B,
      ∃ lB : Spec (.of ((hypersurface F hF).residueField P.1)) ⟶ scheme B,
        IsClosedImmersion lB ∧
        lB ≫ quotientProjMap B =
          (hypersurface F hF).fromSpecResidueField P.1 ≫ hypersurfaceToAmbient F hF ∧
        lB ≫ toBase B =
          (hypersurface F hF).fromSpecResidueField P.1 ≫ hypersurfaceToBase F hF ∧
        (∀ i : Fin 4,
          QuarticNet.actualLineAmbientPulledCoordinateHom
              (hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B) i ≫
            hB.nativeAmbientPositiveOnePullbackIso.hom =
          hB.literalChosenNativeCubicSectionHom i) ∧
        ∃ β : Basis (Fin 4) K
            (SchemeModuleGlobalSectionsOver
              (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K)))
              ((Scheme.Modules.pullback (hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B)).obj
                (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 1))),
          ∀ i : Fin 4, β i =
            QuarticNet.actualLineAmbientPulledCoordinateHom
              (hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B) i := by
  obtain ⟨B, hB, lB, hlB, hAmbient, hBase, hImages⟩ :=
    perfectField_original_closedPoint_exists_twistedCubic_nativeCoordinateImages F hF P hdim hplane
  exact ⟨B, hB, lB, hlB, hAmbient, hBase, hImages,
    hB.nativeAmbientPulledCoordinateBasis,
    fun i => hB.nativeAmbientPulledCoordinateBasis_apply i⟩

end PfaffianDescent
