import PfaffianDescent.VoisinRelativeUniversalDivisor
import PfaffianDescent.AffineSourceChartBaseChange

/-!
# Ideal and quotient base change for Voisin's relative divisor

The universal moving equation defines a closed immersion into the constant
cubic-surface family.  The general closed-immersion base-change theorem
therefore applies to the actual relative zero locus.  The quotient
pushforward comparison needs no flatness; the ideal-module comparison is
available for a flat change of equation parameters.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {K : Type u} [Field K]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (h : E ⟶ projectiveParameters K (Fin 4) 3)

/-- The canonical quotient-pushforward comparison for the actual universal
equation zero locus after any change of equation parameters. -/
theorem fixedCubicSurfaceEquationZeroLocus_isIso_pushforwardBaseChange
    {T : Scheme.{u}} (s : T ⟶ E) :
    IsIso (@closedImmersionPushforwardBaseChangeHom _ _ _
      (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)
      (fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion a ha k h)) := by
  exact @isIso_closedImmersionPushforwardBaseChangeHom_general _ _ _
    (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s)
    (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)
    (fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion a ha k h)

/-- A flat change of equation parameters identifies the pullback of the
actual universal divisor ideal with the ideal of its fibre-product divisor.
This is the canonical ideal-module map, not merely an abstract isomorphism. -/
theorem fixedCubicSurfaceEquationZeroLocus_isIso_idealBaseChange
    {T : Scheme.{u}} (s : T ⟶ E) [Flat s] :
    IsIso (@closedImmersionIdealBaseChangeHom _ _ _
      (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)
      (fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion a ha k h)) := by
  have hflat : Flat (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s) :=
    inferInstance
  exact @isIso_flatClosedImmersionIdealBaseChangeHom_general _ _ _
    (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s)
    hflat
    (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)
    (fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion a ha k h)

end PfaffianDescent
