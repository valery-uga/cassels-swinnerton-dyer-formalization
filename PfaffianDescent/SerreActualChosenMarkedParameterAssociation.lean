import PfaffianDescent.SerreActualClosedPullbackZeroMarkedFibre

/-! Associate a chosen parameter without changing its marked surface point. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u

def serreActualChosenMarkedParameterAssociation
    {Z P Q T U : Scheme.{u}} (z : Z ⟶ Q)
    (r : T ⟶ U) (b : U ⟶ P) (v : P ⟶ Q) :
    pullback z ((r ≫ b) ≫ v) ≅ pullback z (r ≫ (b ≫ v)) :=
  pullback.congrHom rfl (Category.assoc r b v)

@[reassoc]
theorem serreActualChosenMarkedParameterAssociation_hom_fst
    {Z P Q T U : Scheme.{u}} (z : Z ⟶ Q)
    (r : T ⟶ U) (b : U ⟶ P) (v : P ⟶ Q) :
    (serreActualChosenMarkedParameterAssociation z r b v).hom ≫
      pullback.fst z (r ≫ (b ≫ v)) = pullback.fst z ((r ≫ b) ≫ v) := by
  simp only [serreActualChosenMarkedParameterAssociation, pullback.congrHom,
    asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]

theorem serreActualChosenMarkedParameterAssociation_stalk_isField
    {Z P Q T U : Scheme.{u}} (z : Z ⟶ Q)
    (r : T ⟶ U) (b : U ⟶ P) (v : P ⟶ Q)
    (y : (pullback z ((r ≫ b) ≫ v) : Scheme))
    (hy : IsField ((pullback z ((r ≫ b) ≫ v)).presheaf.stalk y)) :
    IsField ((pullback z (r ≫ (b ≫ v))).presheaf.stalk
      ((serreActualChosenMarkedParameterAssociation z r b v).hom y)) :=
  serreActualChosenFibreIso_stalk_isField
    (serreActualChosenMarkedParameterAssociation z r b v) y hy

end PfaffianDescent
