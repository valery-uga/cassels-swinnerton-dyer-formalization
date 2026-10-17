import PfaffianDescent.SerreActualClosedPullbackZeroIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpenSourceIso

/-! The maximal finite-fibre parameter open is the same for the actual
compared closed zero families.  Flatness on that open therefore transfers. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualClosedPullbackZero_goodOpen_eq
    {T X Y Z W P : Scheme.{u}}
    (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (f : T ⟶ X) (g : T ⟶ Y)
    (h : i.ker.comap f = j.ker.comap g) (a : T ⟶ P)
    [IsProper (pullback.fst f i ≫ a)] [IsProper (pullback.fst g j ≫ a)] :
    cubicClosedPointSerreFiniteZeroResidual_goodOpen (pullback.fst f i ≫ a) =
      cubicClosedPointSerreFiniteZeroResidual_goodOpen (pullback.fst g j ≫ a) := by
  let e := serreActualClosedPullbackZeroIso i j f g h
  have hfac : e.hom ≫ (pullback.fst g j ≫ a) = pullback.fst f i ≫ a :=
    serreActualClosedPullbackZeroIso_hom_fst_assoc i j f g h a
  simpa only [hfac] using
    cubicClosedPointSerreFiniteZeroResidual_goodOpen_comp_iso (pullback.fst g j ≫ a) e

theorem serreActualClosedPullbackZero_goodOpen_flat
    {T X Y Z W P : Scheme.{u}}
    (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (f : T ⟶ X) (g : T ⟶ Y)
    (h : i.ker.comap f = j.ker.comap g) (a : T ⟶ P)
    [IsProper (pullback.fst f i ≫ a)] [IsProper (pullback.fst g j ≫ a)]
    [Flat ((pullback.fst g j ≫ a) ∣_
      cubicClosedPointSerreFiniteZeroResidual_goodOpen (pullback.fst g j ≫ a))] :
    Flat ((pullback.fst f i ≫ a) ∣_
      cubicClosedPointSerreFiniteZeroResidual_goodOpen (pullback.fst f i ≫ a)) := by
  let e := serreActualClosedPullbackZeroIso i j f g h
  have hfac : e.hom ≫ (pullback.fst g j ≫ a) = pullback.fst f i ≫ a :=
    serreActualClosedPullbackZeroIso_hom_fst_assoc i j f g h a
  have hf := cubicClosedPointSerreFiniteZeroResidual_flat_restrict_comp_iso
    (pullback.fst g j ≫ a) e
    (cubicClosedPointSerreFiniteZeroResidual_goodOpen (pullback.fst g j ≫ a))
  rw [hfac] at hf
  rw [serreActualClosedPullbackZero_goodOpen_eq i j f g h a]
  exact hf

end PfaffianDescent
