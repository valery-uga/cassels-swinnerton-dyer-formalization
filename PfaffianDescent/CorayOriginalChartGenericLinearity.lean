import PfaffianDescent.CorayOriginalChartGenericCompatibility

/-! Source-only / unverified. The EXISTING native chart scalar action
agrees with multiplication by the actual chart base coefficient. The
generic germ is then linear for the independently defined original-pi
function-field action, without a new action or a presumed compatibility. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u v

section
variable {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]
variable (G : ℕ → Submodule K A) [GradedRing G] {z : A}

/-- The installed homogeneous-localization action is the chart base
coefficient multiplication. Injective valuation proves the equality. -/
theorem gradedChartNative_smul_eq_baseMap_mul (c : K) (r : Away G z) :
    c • r = AllCharacteristics.GradedChart.baseMap G (z := z) c * r := by
  apply val_injective (.powers z)
  simp only [val_smul, val_mul, AllCharacteristics.GradedChart.val_baseMap,
    Algebra.smul_def]
  rw [← Localization.mk_algebraMap (M := .powers z) (A := K) c,
    Localization.mk_one_eq_algebraMap]

end

section
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  [IsIntegral (hypersurface p hp)] (j : Fin 4)
  [Nonempty (chartι (equationIdeal p hp) j).opensRange]

/-- Actual chart scalars become the independently existing ORIGINAL-pi
function-field scalars, through the proved coefficient diagram. -/
theorem cubicChartGenericEvaluation_native_smul (c : K)
    (r : ChartRing (equationIdeal p hp) j) :
    (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)) (c • r) =
      schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp) c *
        (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)) r := by
  have hchart : c • r = chartBaseMap (equationIdeal p hp) j c * r :=
    gradedChartNative_smul_eq_baseMap_mul (grading (equationIdeal p hp)) c r
  rw [hchart, map_mul]
  have hc := RingHom.congr_fun (cubicChartGenericEvaluation_coefficient_eq p hp j) c
  exact congrArg (fun a => a *
    (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)) r) hc

end

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]

/-- The bounded ORIGINAL family now evaluates linearly into the ORIGINAL
surface function field with its independently fixed original-pi K action.
This is the SAME function as packet002, with scalar compatibility proved. -/
def cubicThroughPointGenericLinearEvaluation :
    cubicThroughCoordinateSections p hp n y hpy →ₗ[K]
      SchemeFunctionFieldOver (hypersurfaceToBase p hp) where
  toFun s := (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange))
    (cubicThroughPointChartEvaluation p hp n y hpy j s)
  map_add' s t := by
    change (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange))
      (cubicThroughPointChartEvaluation p hp n y hpy j (s + t)) =
        (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange))
          (cubicThroughPointChartEvaluation p hp n y hpy j s) +
        (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange))
          (cubicThroughPointChartEvaluation p hp n y hpy j t)
    rw [map_add, map_add]
  map_smul' c s := by
    change (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange))
      (cubicThroughPointChartEvaluation p hp n y hpy j (c • s)) =
        schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp) c *
          (@affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange))
            (cubicThroughPointChartEvaluation p hp n y hpy j s)
    rw [map_smul]
    exact cubicChartGenericEvaluation_native_smul p hp j c _

/-- True native injectivity, inherited from prime-cone normalization and
the actual original generic germ, with no rank certificate hypothesis. -/
theorem cubicThroughPointGenericLinearEvaluation_injective (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Function.Injective (cubicThroughPointGenericLinearEvaluation p hp n y hpy j) :=
  ((@affineChartGenericEvaluation_injective
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange))).comp
    (cubicThroughPointChartEvaluation_injective p hp hp0 n y hpy j)

end
end PfaffianDescent.Coray
end
