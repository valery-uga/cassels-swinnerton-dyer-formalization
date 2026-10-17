import AllCharacteristics.ConfigurationBaseChangeSmooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Actual base changes of ordered configuration powers are integral -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceConfiguration_power_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (n : ℕ) :
    LocallyOfFiniteType (orderedFamilyPowerOver f n).hom := by
  induction n with
  | zero =>
    change LocallyOfFiniteType (𝟙 S)
    infer_instance
  | succ n ih =>
    letI := ih
    change LocallyOfFiniteType (pullback.fst f (orderedFamilyPowerOver f n).hom ≫ f)
    infer_instance

theorem serreIncidenceConfiguration_pullback_power_integral
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [LocallyOfFiniteType f]
    [IsIntegral T] [IsLocallyNoetherian T] (n : ℕ) :
    IsIntegral (pullback (orderedFamilyPowerOver f n).hom g) := by
  induction n with
  | zero =>
    change IsIntegral (pullback (𝟙 S) g)
    exact IsIntegral.of_isIso (inv (pullback.snd (𝟙 S) g))
  | succ n ih =>
    let h := (orderedFamilyPowerOver f n).hom
    let Y := pullback h g
    letI : IsIntegral Y := ih
    letI : LocallyOfFiniteType h := serreIncidenceConfiguration_power_locallyOfFiniteType f n
    letI : IsLocallyNoetherian Y := inferInstanceAs (IsLocallyNoetherian (pullback h g))
    letI : IsIntegral (pullback f (pullback.fst h g ≫ h)) := inferInstance
    change IsIntegral (pullback (pullback.fst f h ≫ f) g)
    rw [pullback.condition]
    exact IsIntegral.of_isIso (pullbackAssoc f h h g).inv

end PfaffianDescent
