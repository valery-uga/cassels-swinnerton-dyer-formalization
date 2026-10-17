import AllCharacteristics.ProjectivePoints
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Rational maps from homogeneous function-field coordinates

This file turns a nonzero homogeneous solution over the function field of an
integral source into an actual rational map to a projective hypersurface.  It
is the scheme-theoretic bridge used by explicit secant parametrizations.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

universe u

/-- A nonzero homogeneous solution over a source scheme's function field
spreads out to a rational map into the corresponding projective hypersurface. -/
theorem rationalMap_of_functionField_coordinates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (a : Fin 4 → X.functionField) (ha : a ≠ 0)
    (hpa : p.eval₂ φ.hom a = 0) :
    ∃ f : X ⤏ hypersurface p hp,
      f.compHom (hypersurfaceToBase p hp) = xbase.toRationalMap := by
  letI : X.Over (Spec (.of k)) := ⟨xbase⟩
  letI : (hypersurface p hp).Over (Spec (.of k)) := ⟨hypersurfaceToBase p hp⟩
  letI : (Spec X.functionField).Over (Spec (.of k)) :=
    ⟨X.fromSpecStalk _ ≫ xbase⟩
  letI : LocallyOfFiniteType (hypersurfaceToBase p hp) := by infer_instance
  letI : LocallyOfFiniteType ((hypersurface p hp) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (hypersurfaceToBase p hp)
    infer_instance
  obtain ⟨q, hq⟩ := hypersurface_point_of_coordinates φ.hom p hp a ha hpa
  have hqOver : q.IsOver (Spec (.of k)) := by
    rw [Scheme.Hom.isOver_iff]
    exact hq.trans hφ
  let fq : { f : Spec X.functionField ⟶ hypersurface p hp // f.IsOver (Spec (.of k)) } :=
    ⟨q, hqOver⟩
  let f := (Scheme.RationalMap.equivFunctionFieldOver (X := X)
    (Y := hypersurface p hp) (S := Spec (.of k))) fq
  refine ⟨f.1, ?_⟩
  exact Scheme.RationalMap.isOver_iff.mp f.2

end HomogeneousProjective
end AllCharacteristics
