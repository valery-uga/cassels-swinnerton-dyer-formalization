import PfaffianDescent.CorayProjectiveEvaluationLinearForm
import Mathlib.RingTheory.Localization.Away.Basic

/-! Native projective evaluation on the denominator-nonzero open, with literal
linear hyperplane pullback equation over the unchanged coefficient map. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K R : Type u} [CommRing K] [CommRing R] {σ : Type} [Fintype σ]

/-- The native chart hom on Spec of the localization at a coordinate. -/
def nativeLocalizedProjectiveChartMap (f : K →+* R) (x : σ → R) (a : σ) :
    ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a →+*
      Localization.Away (x a) :=
  projectiveChartMap ((algebraMap R (Localization.Away (x a))).comp f)
    (fun i => algebraMap R (Localization.Away (x a)) (x i) *
      IsLocalization.Away.invSelf (x a)) a
    (IsLocalization.Away.mul_invSelf (x a))

/-- The actual scheme map retains the native localization source. -/
def nativeLocalizedProjectiveChartPoint (f : K →+* R) (x : σ → R) (a : σ) :
    Spec (.of (Localization.Away (x a))) ⟶
      scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) :=
  Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap f x a)) ≫
    chartι (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a

/-- Base, coordinates, the WHOLE linear equation and ideal-membership
pullback are computed on the SAME native denominator-nonzero affine open.
The inverse coordinate is a unit, so no reduced-support substitution occurs. -/
theorem nativeLocalizedProjectiveChartMap_hyperplane_pullback001
    (f : K →+* R) (x : σ → R) (a : σ) :
    (nativeLocalizedProjectiveChartMap f x a).comp
      (chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a) =
        (algebraMap R (Localization.Away (x a))).comp f ∧
    (∀ i, nativeLocalizedProjectiveChartMap f x a
      (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a i) =
        algebraMap R (Localization.Away (x a)) (x i) * IsLocalization.Away.invSelf (x a)) ∧
    (∀ c : σ → K,
      nativeLocalizedProjectiveChartMap f x a (projectiveChartLinearForm a c) =
        algebraMap R (Localization.Away (x a)) (∑ i, f (c i) * x i) *
          IsLocalization.Away.invSelf (x a)) ∧
    (∀ (c : σ → K) (T : Ideal (Localization.Away (x a))),
      nativeLocalizedProjectiveChartMap f x a (projectiveChartLinearForm a c) ∈ T ↔
        algebraMap R (Localization.Away (x a)) (∑ i, f (c i) * x i) ∈ T) := by
  classical
  let S := Localization.Away (x a)
  let l : R →+* S := algebraMap R S
  let inv : S := IsLocalization.Away.invSelf (x a)
  have hBase : (nativeLocalizedProjectiveChartMap f x a).comp
      (chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a) = l.comp f := by
    ext k
    exact projectiveChartMap_baseMap (l.comp f) (fun i => l (x i) * inv) a
      (IsLocalization.Away.mul_invSelf (x a)) k
  have hCoordinates (i : σ) : nativeLocalizedProjectiveChartMap f x a
      (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a i) =
        l (x i) * inv :=
    projectiveChartMap_coordinate (l.comp f) (fun i => l (x i) * inv) a
      (IsLocalization.Away.mul_invSelf (x a)) i
  have hForm (c : σ → K) : nativeLocalizedProjectiveChartMap f x a
      (projectiveChartLinearForm a c) = l (∑ i, f (c i) * x i) * inv := by
    simp only [projectiveChartLinearForm, map_sum, map_mul]
    calc
      _ = ∑ i, l (f (c i)) * (l (x i) * inv) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hCoordinates]
        have h := RingHom.congr_fun hBase (c i)
        change nativeLocalizedProjectiveChartMap f x a
          (chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a (c i)) =
            l (f (c i)) at h
        rw [h]
      _ = (∑ i, l (f (c i)) * l (x i)) * inv := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact (mul_assoc _ _ _).symm
      _ = _ := by rfl
  refine ⟨hBase, hCoordinates, hForm, ?_⟩
  intro c T
  constructor
  · intro h
    have hMul := Ideal.mul_mem_right (l (x a)) T h
    have hInv : inv * l (x a) = 1 := by
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf (x a)
    rw [hForm, mul_assoc, hInv, mul_one] at hMul
    exact hMul
  · intro h
    rw [hForm]
    exact Ideal.mul_mem_right inv T h

/-- Equality of the literal PRINCIPAL IDEALS, retaining nilpotents and
multiplicities of the hyperplane pullback, not merely its reduced support. -/
theorem nativeLocalizedProjectiveChartMap_hyperplaneIdeal_eq001
    (f : K →+* R) (x : σ → R) (a : σ) (c : σ → K) :
    Ideal.span ({nativeLocalizedProjectiveChartMap f x a (projectiveChartLinearForm a c)} :
      Set (Localization.Away (x a))) =
        Ideal.span ({algebraMap R (Localization.Away (x a)) (∑ i, f (c i) * x i)} :
          Set (Localization.Away (x a))) := by
  have h := (nativeLocalizedProjectiveChartMap_hyperplane_pullback001 f x a).2.2.2 c
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (h _).mpr (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (h _).mp (Ideal.subset_span (Set.mem_singleton _))

/-- The explicit localized projective map is over the ORIGINAL coefficient
hom, not an independently chosen localization scalar structure. -/
theorem nativeLocalizedProjectiveChartPoint_toBase001
    (f : K →+* R) (x : σ → R) (a : σ) :
    nativeLocalizedProjectiveChartPoint f x a ≫
      toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) =
        Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away (x a))).comp f)) := by
  change (Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap f x a)) ≫
    chartι (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a) ≫ _ = _
  rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((nativeLocalizedProjectiveChartMap f x a).comp
    (chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a))) = _
  rw [(nativeLocalizedProjectiveChartMap_hyperplane_pullback001 f x a).1]

end PfaffianDescent.Coray
