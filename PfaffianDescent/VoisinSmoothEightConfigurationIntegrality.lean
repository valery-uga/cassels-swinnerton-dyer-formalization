import PfaffianDescent.VoisinGeometricEightGoodPoint
import PfaffianDescent.VoisinGenericCubicResidual

/-!
# Integral eight-point configuration spaces of a smooth cubic

The geometric detecting configuration gives the nonemptiness required for
integrality of the ordered and unordered configuration spaces.  Thus these
generic spaces do not require a separately supplied finite étale degree-eight
subscheme.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero smooth cubic has a nonempty ordered eight-point configuration
space over any characteristic-zero ground field. -/
theorem nonempty_orderedCubicConfiguration_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    Nonempty (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left := by
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  exact ⟨Classical.choose
    (exists_smoothCubic_orderedEight_goodPoint p hp hpne)⟩

/-- The ordered eight-point configuration space of a nonzero smooth cubic is
integral, without assuming an embedded finite étale degree-eight subscheme. -/
theorem isIntegral_orderedCubicConfiguration_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left := by
  letI : Infinite K := CharZero.infinite K
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : GeometricallyIntegral (toBase (equationIdeal p hp)) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite p hp hpne
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : UniversallyOpen (toBase (equationIdeal p hp)) := inferInstance
  letI : LocallyOfFiniteType (toBase (equationIdeal p hp)) := inferInstance
  letI : Nonempty (orderedFamilyConfigurationOver
      (toBase (equationIdeal p hp)) 8).left :=
    nonempty_orderedCubicConfiguration_of_smooth p hp hpne
  change IsIntegral (orderedFamilyConfigurationOver
    (toBase (equationIdeal p hp)) 8).left
  exact isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral
    (toBase (equationIdeal p hp)) 8

/-- The unordered generic eight-point configuration base of a nonzero smooth
cubic is integral, with nonemptiness supplied by the detecting geometric
configuration. -/
theorem isIntegral_cubicConfigurationBase_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (cubicConfigurationBase p hp 8) := by
  letI : Infinite K := CharZero.infinite K
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : GeometricallyIntegral (toBase (equationIdeal p hp)) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite p hp hpne
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : UniversallyOpen (toBase (equationIdeal p hp)) := inferInstance
  letI : LocallyOfFiniteType (toBase (equationIdeal p hp)) := inferInstance
  letI : Nonempty (orderedFamilyConfigurationOver
      (toBase (equationIdeal p hp)) 8).left :=
    nonempty_orderedCubicConfiguration_of_smooth p hp hpne
  exact isIntegral_cubicConfigurationBase_of_geometricallyIntegral p hp 8

end PfaffianDescent
