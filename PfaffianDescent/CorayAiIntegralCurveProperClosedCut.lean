import PfaffianDescent.CorayIntegralCurveClosedSupportFinite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option autoImplicit false

/-- One actual point outside a closed cut derives generic-point avoidance;
the full original curve supplies finiteness and closed points of that cut. -/
theorem integralCurve_proper_closedCut_finite_closedPoints001
    (C : Scheme.{u}) [IsIntegral C] [NoetherianSpace C]
    (hDim : ∀ x : C, Ring.DimensionLEOne (C.presheaf.stalk x))
    (Z : Set C) (hZ : IsClosed Z) (x : C) (hx : x ∉ Z) :
    Z.Finite ∧ ∀ z ∈ Z, IsClosed ({z} : Set C) := by
  have hg : genericPoint C ∉ Z := by
    intro h
    have hAll := closure_minimal (Set.singleton_subset_iff.mpr h) hZ
    rw [genericPoint_closure] at hAll
    exact hx (hAll (Set.mem_univ x))
  exact integralCurve_closed_avoiding_generic_finite_and_closedPoints C hDim Z hZ hg

/-- Closed points of a genuine curve cut are closed in its original ambient
scheme under the actual closed immersion. -/
theorem integralCurve_proper_closedCut_ambient_closedImages001
    (C Y : Scheme.{u}) [IsIntegral C] [NoetherianSpace C]
    (i : C ⟶ Y) [IsClosedImmersion i]
    (hDim : ∀ x : C, Ring.DimensionLEOne (C.presheaf.stalk x))
    (H : Set Y) (hH : IsClosed H) (x : C) (hx : i x ∉ H) :
    (i ⁻¹' H).Finite ∧ ∀ z : C, i z ∈ H → IsClosed ({i z} : Set Y) := by
  obtain ⟨hFinite, hClosed⟩ := integralCurve_proper_closedCut_finite_closedPoints001
    C hDim (i ⁻¹' H) (hH.preimage i.continuous) x hx
  refine ⟨hFinite, ?_⟩
  intro z hz
  simpa only [Set.image_singleton] using
    i.isClosedEmbedding.isClosedMap ({z} : Set C) (hClosed z hz)

/-- Two distinct actual ambient images on an open of the WHOLE original
source contradict its integrality when they lie in this proper curve cut.
Closedness of every actual image is derived from the curve cut. -/
theorem wholeScheme_open_sameCurveCut_twoImages_not_integral001
    (X C Y : Scheme.{u}) [IsIntegral C] [NoetherianSpace C]
    (i : C ⟶ Y) [IsClosedImmersion i]
    (hDim : ∀ x : C, Ring.DimensionLEOne (C.presheaf.stalk x))
    (H : Set Y) (hH : IsClosed H) (outside : C) (hOutside : i outside ∉ H)
    (U : X.Opens) (f : (U : Scheme) ⟶ C)
    (hCut : ∀ x : (U : Scheme), i (f x) ∈ H)
    (x₀ x₁ : (U : Scheme)) (hDistinct : i (f x₀) ≠ i (f x₁)) :
    ¬ IsIntegral X := by
  intro hX
  letI : IsIntegral X := hX
  letI : Nonempty (U : Scheme) := ⟨x₀⟩
  letI : IsIntegral (U : Scheme) := isIntegral_of_isOpenImmersion U.ι
  have hImages := (integralCurve_proper_closedCut_ambient_closedImages001
    C Y i hDim H hH outside hOutside).2
  let g : (U : Scheme) ⟶ Y := f ≫ i
  have hClosed : IsClosed ({g (genericPoint (U : Scheme))} : Set Y) :=
    hImages _ (hCut _)
  have hEqual (x : (U : Scheme)) : g x = g (genericPoint (U : Scheme)) := by
    have hSpecializes : g (genericPoint (U : Scheme)) ⤳ g x :=
      (genericPoint_specializes x).map g.continuous
    have hx := specializes_iff_mem_closure.mp hSpecializes
    rw [hClosed.closure_eq] at hx
    exact Set.mem_singleton_iff.mp hx
  exact hDistinct ((hEqual x₀).trans (hEqual x₁).symm)

end PfaffianDescent.Coray
