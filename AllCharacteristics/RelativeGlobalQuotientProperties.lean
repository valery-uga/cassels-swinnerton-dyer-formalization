import AllCharacteristics.RelativeGlobalQuotientChartPullback
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Integral and finite geometry of the actual global quotient

The actual chart pullback squares transfer the proved affine invariant-ring
properties to the global quotient morphism. No global quotient property is
assumed as data in this argument.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] (n : ℕ) [hSep : X.IsSeparated]

/-- Properties local on the target pass from the actual invariant-spectrum
chart morphisms to the constructed global quotient morphism. -/
theorem property_orderedCommonOpenGlobalQuotientMap
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ U : X.affineOpens, P (commonOpenTupleQuotientMap f U.val n U.property)) :
    P (orderedCommonOpenGlobalQuotientMap f n) := by
  apply IsZariskiLocalAtTarget.of_openCover (commonOpenTupleQuotientGluedCover f n)
  intro U
  change X.affineOpens at U
  change P (pullback.snd (orderedCommonOpenGlobalQuotientMap f n)
    (commonOpenTupleQuotientGluedChart f n U))
  have h := isPullback_orderedCommonOpenGlobalQuotientMap_chart f n U
  rw [← h.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  exact hP U

/-- The constructed global quotient map is integral in every characteristic. -/
instance isIntegralHom_orderedCommonOpenGlobalQuotientMap :
    IsIntegralHom (orderedCommonOpenGlobalQuotientMap f n) := by
  let : IsZariskiLocalAtTarget (@IsIntegralHom : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  exact property_orderedCommonOpenGlobalQuotientMap f n (@IsIntegralHom : MorphismProperty Scheme.{u})
    (fun U ↦ isIntegralHom_commonOpenTupleQuotientMap f U.val n U.property)

/-- For a locally finite-type family the constructed global quotient map is finite. -/
instance isFinite_orderedCommonOpenGlobalQuotientMap [LocallyOfFiniteType f] :
    IsFinite (orderedCommonOpenGlobalQuotientMap f n) := by
  let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  exact property_orderedCommonOpenGlobalQuotientMap f n (@IsFinite : MorphismProperty Scheme.{u})
    (fun U ↦ isFinite_commonOpenTupleQuotientMap f U.val n U.property)

/-- For a locally finite-type family the constructed global quotient map is proper. -/
instance isProper_orderedCommonOpenGlobalQuotientMap [LocallyOfFiniteType f] :
    IsProper (orderedCommonOpenGlobalQuotientMap f n) := by
  infer_instance

end AllCharacteristics
