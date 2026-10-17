import PfaffianDescent.ConicCubicCommonFactor
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import AllCharacteristics.ProjectivePoints

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K] {n : ℕ}

/-- Evaluation of a homogeneous linear form is a linear functional on coordinates. -/
theorem homogeneous_linear_eval_exists (l : MvPolynomial (Fin n) K) (hl : l.IsHomogeneous 1) :
    ∃ E : (Fin n → K) →ₗ[K] K, ∀ x, MvPolynomial.eval x l = E x := by
  have hs : l ∈ Submodule.span K (Set.range (X : Fin n → MvPolynomial (Fin n) K)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hl
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hs
  let E : (Fin n → K) →ₗ[K] K := ∑ i, c i • LinearMap.proj i
  refine ⟨E, fun x => ?_⟩
  rw [← hc]
  simp [E]

/-- A homogeneous linear equation in at least two coordinates has a nonzero
solution over its coefficient field. -/
theorem homogeneous_linear_has_nonzero_zero (l : MvPolynomial (Fin n) K)
    (hl : l.IsHomogeneous 1) (hn : 1 < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x l = 0 := by
  obtain ⟨E, hE⟩ := homogeneous_linear_eval_exists l hl
  have hker : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hn)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨x, hx0, (hE x).trans hx⟩

/-- A polynomial with a homogeneous linear factor has a rational projective zero. -/
theorem linear_factor_has_nonzero_zero (f l : MvPolynomial (Fin n) K)
    (hl : l.IsHomogeneous 1) (hd : l ∣ f) (hn : 1 < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  obtain ⟨x, hx, hxl⟩ := homogeneous_linear_has_nonzero_zero l hl hn
  obtain ⟨g, rfl⟩ := hd
  refine ⟨x, hx, ?_⟩
  rw [map_mul, hxl, zero_mul]

/-- The common-component branch of the conic/cubic construction supplies a
rational zero, with all polynomial factors defined over the ground field. -/
theorem conic_cubic_common_factor_has_nonzero_zero
    {q f d : MvPolynomial (Fin 3) K} (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hf0 : f ≠ 0) (hd : ¬ IsUnit d) (hdq : d ∣ q) (hdf : d ∣ f) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  obtain ⟨l, _, hl, hlf⟩ := conic_cubic_common_factor_linear_divisor hq hf hq0 hf0 hd hdq hdf
  exact linear_factor_has_nonzero_zero f l hl hlf (by decide)

end
section
open AlgebraicGeometry CategoryTheory AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]

/-- The common-component argument produces a section of the actual plane-cubic scheme. -/
theorem conic_cubic_common_factor_section
    {q f d : MvPolynomial (Fin 3) K} (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hf0 : f ≠ 0) (hd : ¬ IsUnit d) (hdq : d ∣ q) (hdf : d ∣ f) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨x, hx, hxf⟩ := conic_cubic_common_factor_has_nonzero_zero hq hf hq0 hf0 hd hdq hdf
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id K) f hf x hx hxf
  exact ⟨s, by simpa using hs⟩

/-- Failure of relative primality in the coplanar argument gives a section;
the identically zero plane restriction is included. -/
theorem conic_cubic_not_relPrime_section
    {q f : MvPolynomial (Fin 3) K} (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : ¬ IsRelPrime q f) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  classical
  by_cases hf0 : f = 0
  · obtain ⟨x, hx, _⟩ := homogeneous_linear_has_nonzero_zero
      (0 : MvPolynomial (Fin 3) K) (isHomogeneous_zero _ _ 1) (by decide)
    have hxf : MvPolynomial.eval x f = 0 := by rw [hf0, map_zero]
    obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id K) f hf x hx hxf
    exact ⟨s, by simpa using hs⟩
  · change ¬ ∀ d : MvPolynomial (Fin 3) K, d ∣ q → d ∣ f → IsUnit d at hrel
    push_neg at hrel
    obtain ⟨d, hdq, hdf, hd⟩ := hrel
    exact conic_cubic_common_factor_section hq hf hq0 hf0 hd hdq hdf

end
end PfaffianDescent
