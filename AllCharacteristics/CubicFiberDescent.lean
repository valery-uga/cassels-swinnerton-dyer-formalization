import AllCharacteristics.HomogeneousFiberCoordinates
import PfaffianDescent.QuarticMultivariate

/-!
# Cubic descent from actual pullback-fiber cycles

An effective cycle on the actual scheme-theoretic fiber is converted to
coordinates over its own residue fields, preserving degrees. The quartic and
quintic coordinate theorems therefore apply without first identifying the fiber
with another Proj construction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- An actual cycle of degree four or five on a characteristic-zero fiber of
a cubic hypersurface gives a nonzero solution of the specialized equation. -/
theorem hypersurface_fiber_coordinates_of_effective_degree_four_or_five
    {R k : Type u} [CommRing R] [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) (b : R →+* k)
    (z : EffectiveZeroCycle
      (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))))
    (hz : EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z = 4 ∨
      EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z = 5) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval₂ b y = 0 := by
  classical
  let f := hypersurfaceToBase p hp
  let B := Spec.map (CommRingCat.ofHom b)
  let Y := pullback f B
  let g := pullback.snd f B
  let ι := z.support
  let L : ι → Type u := fun x ↦ Y.residueField x.1.1
  let : ∀ x : ι, Field (L x) := fun x ↦ inferInstance
  let : ∀ x : ι, Algebra k (L x) := fun x ↦ pointAlgebra g x.1.1
  have : ∀ x : ι, Module.Finite k (L x) := fun x ↦ closedPoint_moduleFinite g x.1
  have hc : ∀ x : ι, ∃ v : Fin 4 → L x, v ≠ 0 ∧
      (p.map b).eval₂ (algebraMap k (L x)) v = 0 :=
    fun x ↦ hypersurface_fiber_residueField_coordinates p hp b x.1.1
  choose v hv he using hc
  have hd : ∑ x : ι, z x.1 * Module.finrank k (L x) = EffectiveZeroCycle.degree g z :=
    (EffectiveZeroCycle.degree_eq_sum_finrank g z).symm
  have hsol : ∃ y : Fin 4 → k, y ≠ 0 ∧ (p.map b).eval y = 0 := by
    rcases hz with h₄ | h₅
    · exact PfaffianDescent.homogeneous_cubic_effective_degree_four_to_point
        L (p.map b) (hp.map b) (fun x ↦ z x.1) v
        (fun x _ ↦ hv x) (fun x _ ↦ he x) (hd.trans h₄)
    · exact PfaffianDescent.homogeneous_cubic_effective_degree_five_to_point
        L (p.map b) (hp.map b) (fun x ↦ z x.1) v
        (fun x _ ↦ hv x) (fun x _ ↦ he x) (hd.trans h₅)
  obtain ⟨y, hy, hey⟩ := hsol
  refine ⟨y, hy, ?_⟩
  rw [MvPolynomial.eval₂_eq_eval_map]
  exact hey

/-- An actual effective cycle of degree four or five on a characteristic-zero
fiber gives a rational section of that same pullback fiber. -/
theorem hypersurface_fiber_section_of_effective_degree_four_or_five
    {R k : Type u} [CommRing R] [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) (b : R →+* k)
    (z : EffectiveZeroCycle
      (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))))
    (hz : EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z = 4 ∨
      EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z = 5) :
    ∃ q : Spec (.of k) ⟶
        pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)),
      q ≫ pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) = 𝟙 _ :=
  (hypersurface_fiber_section_iff_coordinates p hp b).mpr
    (hypersurface_fiber_coordinates_of_effective_degree_four_or_five p hp b z hz)

end AllCharacteristics
