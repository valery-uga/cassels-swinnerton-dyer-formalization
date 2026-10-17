import PfaffianDescent.GroundTwistedCubicNativeCoordinateImages
import PfaffianDescent.CasselsOriginalPointContainingTwistedCubic

/-! SOURCE ONLY. Original perfect-field P internally constructs its SAME
containing curve/presentation and exact literal native cubic image of every
ambient coordinate. No desired curve, bundle or section-image premise is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original degree4/5 Cassels point, exact original residue-field immersion,
SAME selected ground parametrization and ALL FOUR literal native coordinate images. -/
theorem perfectField_original_closedPoint_exists_twistedCubic_nativeCoordinateImages
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
        ∀ i : Fin 4,
          QuarticNet.actualLineAmbientPulledCoordinateHom
              (hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B) i ≫
            hB.nativeAmbientPositiveOnePullbackIso.hom =
          hB.literalChosenNativeCubicSectionHom i := by
  obtain ⟨B, hB, lB, hlB, hAmbient, hBase⟩ :=
    perfectField_original_closedPoint_exists_twistedCubic_ambient_containment F hF P hdim hplane
  exact ⟨B, hB, lB, hlB, hAmbient, hBase,
    fun i => hB.nativeAmbientPositiveOnePullbackIso_coordinate i⟩

end PfaffianDescent
