import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_isField_of_injective_localHom
    {A F : Type*} [CommRing A] [IsLocalRing A] [Field F]
    (q : A →+* F) [IsLocalHom q] (hq : Function.Injective q) : IsField A := by
  apply IsLocalRing.isField_iff_maximalIdeal_eq.mpr
  apply le_antisymm _ bot_le
  intro a ha
  have hqa := map_nonunit q a ha
  rw [IsLocalRing.maximalIdeal_eq_bot] at hqa
  exact hq (by simpa using hqa)

theorem cubicClosedPointSerreFiniteZeroResidual_flat_stalk_isField
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X)
    (hx : IsField (X.presheaf.stalk x)) : IsField (Y.presheaf.stalk (f x)) := by
  letI : Field (X.presheaf.stalk x) := hx.toField
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact cubicClosedPointSerreFiniteZeroResidual_isField_of_injective_localHom
    (f.stalkMap x).hom (‹RingHom.FaithfullyFlat _›.injective)

theorem cubicClosedPointSerreFiniteZeroResidual_flat_surjective_stalks_isField
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    (hx : ∀ x : X, IsField (X.presheaf.stalk x)) (y : Y) :
    IsField (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := (surjective_iff f).mp inferInstance y
  exact cubicClosedPointSerreFiniteZeroResidual_flat_stalk_isField f x (hx x)

end PfaffianDescent
