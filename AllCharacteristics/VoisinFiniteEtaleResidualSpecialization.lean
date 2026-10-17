import AllCharacteristics.FiniteEtaleTuplePoint
import AllCharacteristics.FiniteEtaleConfigurationGenericSpecialization
import AllCharacteristics.VoisinGenericCubicConfiguration

/-!
# Specializing a finite étale residual from the generic cubic configuration

This file composes coefficient base change, passage from a finite étale
residual to an unordered tuple, and specialization from the generic
configuration field.  The argument works in arbitrary positive input and
residual degrees; the degree-eight/four case is a specialization.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite étale residual of degree `m` over the generic configuration
field of a finite étale degree-`n` subscheme specializes to an effective
degree-`m` cycle on the original cubic. -/
theorem effectiveCycle_of_genericFiniteEtaleResidual
    (n m : ℕ)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    [IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left]
    [IsIntegral (cubicConfigurationBase p hp n)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp n ≫
        cubicConfigurationToBase p hp n)
    (R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) m)
    [Etale (R.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))] :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = m := by
  have hsmooth : Smooth (hypersurfaceToBase p hp) := inferInstance
  have hordered : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left :=
    inferInstance
  have hbase : IsIntegral (cubicConfigurationBase p hp n) := inferInstance
  have hD : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    inferInstance
  let B := cubicConfigurationBase p hp n
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp n
  obtain ⟨s, hs⟩ :=
    exists_tupleQuotientPoint_of_finiteEtaleHypersurfaceCoefficientChange
      a.hom p hp m R
  have hs' : s ≫ tupleQuotientToBase (equationIdeal p hp) m =
        cubicConfigurationGenericBaseMap p hp n ≫
          cubicConfigurationToBase p hp n := by
    change s ≫ tupleQuotientToBase (equationIdeal p hp) m = _
    calc
      s ≫ tupleQuotientToBase (equationIdeal p hp) m = Spec.map a := by
        simpa using hs
      _ = cubicConfigurationGenericBaseMap p hp n ≫
          cubicConfigurationToBase p hp n := ha
  let I := equationIdeal p hp
  letI : IsSeparated (toBase I) := isSeparated_homogeneousToBase I
  letI : Smooth (toBase I) := by
    dsimp only [I]
    exact hsmooth
  letI : IsIntegral (orderedFamilyConfigurationOver (toBase I) n).left := by
    dsimp only [I]
    exact hordered
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading I) (toBase I) n).toScheme := by
    dsimp only [I]
    exact hbase
  let D' : FiniteSubschemeDatum (toBase I) n := D
  letI : Etale (D'.val.subschemeι ≫ toBase I) := by
    dsimp only [D', I]
    exact hD
  exact
    effectiveZeroCycle_of_finiteEtaleSubscheme_configurationFunctionFieldTuple
      I n m D' s hs'

/-- The degree-eight/four instance used in Voisin's reduction. -/
theorem effectiveDegreeFourCycle_of_genericFiniteEtaleResidual
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    [IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 8 ≫
        cubicConfigurationToBase p hp 8)
    (R₄ : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 4)
    [Etale (R₄.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))] :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 :=
  effectiveCycle_of_genericFiniteEtaleResidual 8 4 p hp D₈ a ha R₄

end AllCharacteristics.HomogeneousProjective
