import AllCharacteristics.ProjectiveFiberSmoothness
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Descent of projective smoothness through field extensions

The actual pullback of a projective homogeneous scheme is smooth when the
coefficient-changed equations define a smooth scheme. Faithfully flat descent
then reflects this smoothness to the original field. This permits descending
smooth equations to subfields containing their coefficients.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {k K : Type u} {σ : Type} [Field k] [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Smoothness of homogeneous projective equations descends through any
extension of their coefficient field. -/
theorem smooth_toBase_of_smooth_field_changed_ideal
    (f : k →+* K)
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
    [Smooth (toBase J)] : Smooth (toBase I) := by
  have hs := smooth_pullback_of_smooth_changed_ideal f I J h
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (g := Spec.map (CommRingCat.ofHom f))
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hs

/-- A hypersurface smooth after extension of its coefficient field was
already smooth over its original coefficient field. -/
theorem smooth_hypersurfaceToBase_of_smooth_field_map
    (f : k →+* K) (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d)
    [Smooth (hypersurfaceToBase (p.map f) (hp.map f))] :
    Smooth (hypersurfaceToBase p hp) := by
  have : Smooth (toBase (equationIdeal (p.map f) (hp.map f))) :=
    inferInstanceAs (Smooth (hypersurfaceToBase (p.map f) (hp.map f)))
  exact smooth_toBase_of_smooth_field_changed_ideal f (equationIdeal p hp)
    (equationIdeal (p.map f) (hp.map f)) (equationIdeal_map f p hp)

/-- Smoothness of a homogeneous hypersurface is unchanged by extending the
coefficient field. -/
theorem smooth_hypersurfaceToBase_field_map_iff
    (f : k →+* K) (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d) :
    Smooth (hypersurfaceToBase (p.map f) (hp.map f)) ↔
      Smooth (hypersurfaceToBase p hp) := by
  constructor
  · intro h
    exact smooth_hypersurfaceToBase_of_smooth_field_map f p hp
  · intro h
    exact smooth_hypersurfaceToBase_map f p hp

end HomogeneousProjective
end AllCharacteristics
