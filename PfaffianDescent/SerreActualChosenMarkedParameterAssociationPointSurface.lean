import PfaffianDescent.SerreActualChosenMarkedParameterAssociation

/-! Pointwise surface compatibility of the SAME chosen-parameter association. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem serreActualChosenMarkedParameterAssociation_point_surface
    {Z P Q T U X : Scheme.{u}} (z : Z ⟶ Q)
    (r : T ⟶ U) (b : U ⟶ P) (v : P ⟶ Q) (f : Z ⟶ X)
    (y : (pullback z ((r ≫ b) ≫ v) : Scheme)) (x : X)
    (hy : (pullback.fst z ((r ≫ b) ≫ v) ≫ f) y = x) :
    (pullback.fst z (r ≫ (b ≫ v)) ≫ f)
      ((serreActualChosenMarkedParameterAssociation z r b v).hom y) = x := by
  change ((serreActualChosenMarkedParameterAssociation z r b v).hom ≫
    pullback.fst z (r ≫ (b ≫ v)) ≫ f) y = x
  rw [serreActualChosenMarkedParameterAssociation_hom_fst_assoc]
  exact hy

end PfaffianDescent
