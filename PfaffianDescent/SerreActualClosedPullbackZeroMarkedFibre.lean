import PfaffianDescent.SerreActualClosedPullbackZeroParameterChange
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFlatFieldStalk

/-! Marked sections and simple stalks survive the actual zero-fibre comparison. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {T X Y Z W P U V : Scheme.{u}}
variable (i : Z ⟶ X) (j : W ⟶ Y)
variable [IsClosedImmersion i] [IsClosedImmersion j]
variable (f : T ⟶ X) (g : T ⟶ Y)
variable (h : i.ker.comap f = j.ker.comap g)
variable (a : T ⟶ P) (b : U ⟶ P)

@[reassoc]
theorem serreActualClosedPullbackZero_parameterChangeIso_inv_fst :
    (serreActualClosedPullbackZero_parameterChangeIso i j f g h a b).inv ≫
        pullback.fst b (pullback.fst f i ≫ a) =
      pullback.fst b (pullback.fst g j ≫ a) := by
  rw [← serreActualClosedPullbackZero_parameterChangeIso_hom_fst i j f g h a b,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[reassoc]
theorem serreActualClosedPullbackZero_parameterChangeIso_inv_ambient :
    (serreActualClosedPullbackZero_parameterChangeIso i j f g h a b).inv ≫
        pullback.snd b (pullback.fst f i ≫ a) ≫ pullback.fst f i =
      pullback.snd b (pullback.fst g j ≫ a) ≫ pullback.fst g j := by
  rw [← serreActualClosedPullbackZero_parameterChangeIso_hom_ambient i j f g h a b,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A marked map in the old fibre transports to the new fibre with the same
common ambient point. No new incidence membership is assumed. -/
theorem serreActualClosedPullbackZero_parameterChange_marked_ambient
    (m : V ⟶ pullback b (pullback.fst g j ≫ a)) :
    (m ≫ (serreActualClosedPullbackZero_parameterChangeIso i j f g h a b).inv) ≫
        pullback.snd b (pullback.fst f i ≫ a) ≫ pullback.fst f i =
      m ≫ pullback.snd b (pullback.fst g j ≫ a) ≫ pullback.fst g j := by
  simp only [Category.assoc,
    serreActualClosedPullbackZero_parameterChangeIso_inv_ambient]

/-- Simple marked stalks transfer pointwise. The rest of the finite fibre is
allowed to be nonreduced. -/
theorem serreActualClosedPullbackZero_parameterChange_marked_stalk_isField
    (y : (pullback b (pullback.fst g j ≫ a) : Scheme.{u}))
    (hy : IsField ((pullback b (pullback.fst g j ≫ a)).presheaf.stalk y)) :
    IsField ((pullback b (pullback.fst f i ≫ a)).presheaf.stalk
      ((serreActualClosedPullbackZero_parameterChangeIso i j f g h a b).inv y)) := by
  exact cubicClosedPointSerreFiniteZeroResidual_flat_stalk_isField
    (serreActualClosedPullbackZero_parameterChangeIso i j f g h a b).inv y hy

/-- Stalk fields also survive the final exact canonical-fibre identification. -/
theorem serreActualChosenFibreIso_stalk_isField
    {A B : Scheme.{u}} (e : A ≅ B) (y : A)
    (hy : IsField (A.presheaf.stalk y)) : IsField (B.presheaf.stalk (e.hom y)) :=
  cubicClosedPointSerreFiniteZeroResidual_flat_stalk_isField e.hom y hy

end PfaffianDescent
