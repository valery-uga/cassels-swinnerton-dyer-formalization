import PfaffianDescent.CorayBoundedOriginalChartEvaluation
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! Source-only / unverified. The actual affine-chart sections are sent
through their existing section isomorphism and the generic-point germ.
No new function field, scalar action, image-rank or transversality premise
is introduced. Identifying the induced K coefficient map with the original
structure-map germ is a separate next task, not asserted by these roots. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
open scoped PfaffianDescent.Coray

section
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsIntegral X]

/-- Canonical affine-chart-to-function-field map: the actual chart's
section isomorphism followed by the actual generic germ. -/
def affineChartGenericEvaluation
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] [Nonempty i.opensRange] :
    A →+* X.functionField :=
  (X.germToFunctionField i.opensRange).hom.comp
    (((Scheme.ΓSpecIso (.of A)).symm ≪≫
      IsOpenImmersion.ΓIsoTop i).commRingCatIsoToRingEquiv.toRingHom)

/-- Integral geometry proves injectivity of the actual germ map. -/
theorem affineChartGenericEvaluation_injective
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] [Nonempty i.opensRange] :
    Function.Injective (affineChartGenericEvaluation i) :=
  (X.germToFunctionField_injective i.opensRange).comp
    (((Scheme.ΓSpecIso (.of A)).symm ≪≫
      IsOpenImmersion.ΓIsoTop i).commRingCatIsoToRingEquiv.injective)

end

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]

/-- Literal evaluation of an actual bounded through-P section in the
ORIGINAL cubic's function field. The denominator remains X_j^n. -/
def cubicThroughPointGenericEvaluation
    (s : cubicThroughCoordinateSections p hp n y hpy) :
    (hypersurface p hp).functionField :=
  @affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
    (cubicThroughPointChartEvaluation p hp n y hpy j s)

include hp0 in
theorem cubicThroughPointGenericEvaluation_injective :
    Function.Injective (cubicThroughPointGenericEvaluation p hp n y hpy j) :=
  (@affineChartGenericEvaluation_injective
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)).comp
    (cubicThroughPointChartEvaluation_injective p hp hp0 n y hpy j)

include hp0 in
/-- The actual generic coordinate vector is nonzero. This suffices for
a projective function-field point once coefficient compatibility is proved. -/
theorem cubicThroughPointGenericBasis_ne_zero {m : ℕ} (hm : 0 < m)
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) :
    (fun i => cubicThroughPointGenericEvaluation p hp n y hpy j (b i)) ≠ 0 := by
  intro h
  apply cubicThroughPointChartBasis_ne_zero hm p hp hp0 n y hpy j b
  funext i
  apply @affineChartGenericEvaluation_injective
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  simpa only [cubicThroughPointGenericEvaluation, Pi.zero_apply, map_zero]
    using congrFun h i

include hp0 in
/-- The original-K linear relation criterion survives the actual generic
germ. The coefficients stay inside the original chart before applying its
ring hom; this does not silently replace the original field action. -/
theorem cubicThroughPointGenericBasis_relation_iff {m : ℕ}
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (c : Fin m → K) :
    @affineChartGenericEvaluation
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
      (∑ i, c i • cubicThroughPointChartEvaluation p hp n y hpy j (b i)) = 0 ↔ c = 0 := by
  constructor
  · intro h
    apply (cubicThroughPointChartBasis_relation_iff p hp hp0 n y hpy j b c).mp
    apply @affineChartGenericEvaluation_injective
      (ChartRing (equationIdeal p hp) j)
      (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι (equationIdeal p hp) j)
      (isOpenImmersion_chartι (equationIdeal p hp) j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
    simpa only [map_zero] using h
  · rintro rfl
    simp only [Pi.zero_apply]
    have hzero (r : ChartRing (equationIdeal p hp) j) : (0 : K) • r = 0 := by
      exact @Module.zero_smul K (ChartRing (equationIdeal p hp) j) _ _
        (gradedChartNativeModule (grading (equationIdeal p hp))
          (z := coordinate (equationIdeal p hp) j)) r
    have hsum :
        (∑ i : Fin m, (0 : K) •
          cubicThroughPointChartEvaluation p hp n y hpy j (b i)) =
            (0 : ChartRing (equationIdeal p hp) j) := by
      calc
        _ = ∑ _i : Fin m, (0 : ChartRing (equationIdeal p hp) j) :=
          Finset.sum_congr rfl (fun i _ => hzero _)
        _ = 0 := Finset.sum_const_zero
    rw [hsum, map_zero]

end
end PfaffianDescent.Coray
end
