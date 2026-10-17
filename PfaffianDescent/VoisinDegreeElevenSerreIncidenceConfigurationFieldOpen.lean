import PfaffianDescent.VoisinDegreeElevenSerreIncidenceConfigurationFieldPower

/-! # Actual distinct configuration open remains integral after field base change -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceConfiguration_pullback_open_integral
    {X S T : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (g : T ⟶ S)
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [LocallyOfFiniteType f]
    [IsIntegral T] [IsLocallyNoetherian T] (n : ℕ)
    [Nonempty (pullback (orderedFamilyConfigurationOver f n).hom g : Scheme.{u})] :
    IsIntegral (pullback (orderedFamilyConfigurationOver f n).hom g) := by
  let h := (orderedFamilyPowerOver f n).hom
  let i := (orderedFamilyConfigurationOpen f n).ι
  let P := pullback h g
  let Q := pullback i (pullback.fst h g)
  let a := pullbackRightPullbackFstIso h g i
  letI : IsIntegral P := serreIncidenceConfiguration_pullback_power_integral f g n
  letI : Nonempty Q := ⟨a.inv (Classical.choice
    (inferInstance : Nonempty (pullback (orderedFamilyConfigurationOver f n).hom g : Scheme.{u})))⟩
  letI : IsIntegral Q := isIntegral_of_isOpenImmersion (pullback.snd i (pullback.fst h g))
  exact IsIntegral.of_isIso a.hom

end PfaffianDescent
