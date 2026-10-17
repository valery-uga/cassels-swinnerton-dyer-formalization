import PfaffianDescent.CorayExplicitProjectiveEvaluationPoint
import AllCharacteristics.ProjectiveBaseChange

/-! Source-only / unverified. Actual normalized projective evaluation
commutes with coefficient change and a specified map of evaluating fields.
Only the ordinary coefficient-square equality is a generic hypothesis;
the actual tensor caller proves it internally. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K B F G : Type u} [CommRing K] [CommRing B] [Field F] [Field G]
variable {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The existing coefficient morphism on the actual zero-ideal Proj,
retaining the original coefficient hom and its actual target. -/
def projectiveEvaluationCoefficientMap (f : K →+* B) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule σ B)) ⟶
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) :=
  projectiveCoefficientMap f ⊥ ⊥ (by
    change (⊥ : Ideal (MvPolynomial σ K)).map (MvPolynomial.map f) = ⊥
    exact Ideal.map_bot)

/-- The actual chart maps are equal after changing coefficients and
applying the evaluating-field hom. The original normalized coordinates
are preserved, including their original denominator. -/
theorem projectiveEvaluationChartMap_coefficient_naturality
    (f : K →+* B) (φ : K →+* F) (ρ : B →+* G) (ψ : F →+* G)
    (hscalar : ρ.comp f = ψ.comp φ) (x : σ → F) (a : σ)
    (ha : x a ≠ 0) (ha' : ψ (x a) ≠ 0) :
    (projectiveEvaluationChartMap ρ (fun i => ψ (x i)) a ha').comp
      (chartCoefficientMap f
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ B))
        (by change (⊥ : Ideal (MvPolynomial σ K)).map (MvPolynomial.map f) = ⊥
            exact Ideal.map_bot) a) =
      ψ.comp (projectiveEvaluationChartMap φ x a ha) := by
  apply projectiveChartMap_ext a
  · ext c
    simp only [RingHom.comp_apply, chartCoefficientMap_baseMap,
      projectiveEvaluationChartMap]
    rw [projectiveChartMap_baseMap, projectiveChartMap_baseMap]
    exact RingHom.congr_fun hscalar c
  · intro i
    simp only [RingHom.comp_apply, chartCoefficientMap_coordinate]
    rw [projectiveEvaluationChartMap_coordinate, projectiveEvaluationChartMap_coordinate,
      map_div₀]

/-- The SAME explicit projective point over the changed coefficients
projects to the field-changed original explicit point. -/
theorem projectiveEvaluationPoint_coefficient_naturality
    (f : K →+* B) (φ : K →+* F) (ρ : B →+* G) (ψ : F →+* G)
    (hscalar : ρ.comp f = ψ.comp φ) (x : σ → F) (a : σ)
    (ha : x a ≠ 0) (ha' : ψ (x a) ≠ 0) :
    projectiveEvaluationPoint ρ (fun i => ψ (x i)) a ha' ≫
      projectiveEvaluationCoefficientMap f =
        Spec.map (CommRingCat.ofHom ψ) ≫ projectiveEvaluationPoint φ x a ha := by
  change (Spec.map (CommRingCat.ofHom
    (projectiveEvaluationChartMap ρ (fun i => ψ (x i)) a ha')) ≫
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule σ B)) a) ≫
        projectiveCoefficientMap f ⊥ ⊥ _ =
          Spec.map (CommRingCat.ofHom ψ) ≫
            (Spec.map (CommRingCat.ofHom (projectiveEvaluationChartMap φ x a ha)) ≫
              chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a)
  rw [Category.assoc, chartι_projectiveCoefficientMap, ← Category.assoc,
    ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact congrArg
    (fun g : ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a →+* G =>
      Spec.map (CommRingCat.ofHom g) ≫
        chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a)
    (projectiveEvaluationChartMap_coefficient_naturality f φ ρ ψ hscalar x a ha ha')

end PfaffianDescent.Coray
end
