import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridPulledCoordinates

/-! # Native integrality from the actual extension-field grid configuration -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- An actual extension-field ordered configuration supplies nonemptiness
over the ground field. Smooth cubic geometric integrality then gives the
actual integral ordered and unordered bases. -/
theorem voisinDegreeTenSelectedAvoidance_configuration_integral_of_fieldPoint
    {K L : Type u} [Field K] [CharZero K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left) :
    IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left ∧
      IsIntegral (cubicConfigurationBase p hp n) := by
  let I := equationIdeal p hp
  letI : Infinite K := CharZero.infinite K
  letI : IsSeparated (toBase I) := isSeparated_homogeneousToBase I
  letI : GeometricallyIntegral (toBase I) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite p hp hp0
  letI : Flat (toBase I) := inferInstance
  letI : UniversallyOpen (toBase I) := inferInstance
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : Nonempty (orderedFamilyConfigurationOver (toBase I) n).left :=
    ⟨A (IsLocalRing.closedPoint L)⟩
  exact ⟨isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral (toBase I) n,
    isIntegral_cubicConfigurationBase_of_geometricallyIntegral p hp n⟩

end PfaffianDescent
