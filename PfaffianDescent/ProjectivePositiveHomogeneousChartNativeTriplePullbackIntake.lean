import PfaffianDescent.ProjectivePositiveHomogeneousChartLiteralTripleCocycle

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
variable {X B : Scheme.{u}} (F : X ⟶ B) (U V Z : X.Opens) (n : ℕ) [IsSeparated F]
variable (HU HV : Over B)
variable (etaU : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj HU)
variable (etaV : relativeFiniteFlatHilbertFunctor197 (V.ι ≫ F) n ≅ yoneda.obj HV)

/-- The actual first triple factor IS the original open restriction map,
by its exact projection identity and monomorphism of the actual inclusion. -/
theorem relativeOpenChartParameterTriple_firstFactor_eq_restrict001 :
    (relativeOpenChartParameterTripleToFirstOverlap001 F U V Z n HU etaU).left =
      (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left ∣_
        relativeOpenChartParameterOverlap001 F U Z n HU etaU := by
  let W := relativeOpenChartParameterOverlap001 F U Z n HU etaU
  apply (cancel_mono W.ι).mp
  have h := congrArg (fun g => g.left)
    (relativeOpenChartParameterTripleToFirstOverlap_comp001 F U V Z n HU etaU)
  exact h.trans (morphismRestrict_ι
    (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left W).symm

/-- The literal triple scheme's Cartesian square is CONSTRUCTED from the
original open restriction; no Cartesian or matching outcome is supplied. -/
theorem relativeOpenChartParameterTriple_actualCartesian001 :
    IsPullback (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU).left
      (relativeOpenChartParameterTripleToFirstOverlap001 F U V Z n HU etaU).left
      (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
      (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left := by
  rw [relativeOpenChartParameterTriple_firstFactor_eq_restrict001]
  exact (isPullback_morphismRestrict
    (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
    (relativeOpenChartParameterOverlap001 F U Z n HU etaU)).flip

/-- Actual Scheme isomorphism identifies the ENTIRE triple scheme with
native GlueData's literal pair-inclusion pullback, retaining nilpotents. -/
def relativeOpenChartParameterTripleNativePullbackIso001 :
    (relativeOpenChartParameterTripleTest001 F U V Z n HU etaU).left ≅
      pullback (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
        (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left :=
  (relativeOpenChartParameterTriple_actualCartesian001 F U V Z n HU etaU).isoPullback

/-- Exact first projection of the constructed native pullback comparison. -/
theorem relativeOpenChartParameterTripleNativePullbackIso_hom_fst001 :
    (relativeOpenChartParameterTripleNativePullbackIso001 F U V Z n HU etaU).hom ≫
      pullback.fst (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
        (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left =
      (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU).left :=
  (relativeOpenChartParameterTriple_actualCartesian001 F U V Z n HU etaU).isoPullback_hom_fst

/-- Exact second projection of the constructed native pullback comparison. -/
theorem relativeOpenChartParameterTripleNativePullbackIso_hom_snd001 :
    (relativeOpenChartParameterTripleNativePullbackIso001 F U V Z n HU etaU).hom ≫
      pullback.snd (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
        (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left =
      (relativeOpenChartParameterTripleToFirstOverlap001 F U V Z n HU etaU).left :=
  (relativeOpenChartParameterTriple_actualCartesian001 F U V Z n HU etaU).isoPullback_hom_snd

/-- Exact inverse first projection, needed to form native GlueData.t'. -/
theorem relativeOpenChartParameterTripleNativePullbackIso_inv_first001 :
    (relativeOpenChartParameterTripleNativePullbackIso001 F U V Z n HU etaU).inv ≫
      (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU).left =
      pullback.fst (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
        (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left := by
  let E := relativeOpenChartParameterTripleNativePullbackIso001 F U V Z n HU etaU
  exact (congrArg (fun f => E.inv ≫ f)
    (relativeOpenChartParameterTripleNativePullbackIso_hom_fst001 F U V Z n HU etaU).symm).trans
      (E.inv_hom_id_assoc _)

/-- The two actual maps into V/Z and V/U have identical ORIGINAL HV
projection, by the proved triple and reciprocal factor identities. -/
private theorem relativeOpenChartParameterTriple_nativeTarget_square001 :
    (relativeOpenChartParameterTripleToSecondOverlap001 F U V Z n HU HV etaU etaV).left ≫
      (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left =
    ((relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU).left ≫
      (relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV).left) ≫
        (relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV).left := by
  have hSecond := congrArg (fun g => g.left)
    (relativeOpenChartParameterTripleToSecondOverlap_comp001 F U V Z n HU HV etaU etaV)
  have hReciprocal := congrArg (fun g => g.left)
    (relativeOpenChartParameterOverlapReciprocalMap_comp001 F U V n HU HV etaU etaV)
  have hRight :
      ((relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU).left ≫
        (relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV).left) ≫
          (relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV).left =
      (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU).left ≫
        (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).left :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU).left ≫ f)
        hReciprocal)
  exact hSecond.trans hRight.symm

/-- Native GlueData.t' is CONSTRUCTED between its literal Scheme pullbacks
from the same actual triple factors and reciprocal map; no t' is a premise. -/
def relativeOpenChartParameterNativeTripleMap001 :
    pullback (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
      (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left ⟶
    pullback (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left
      (relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV).left :=
  (relativeOpenChartParameterTripleNativePullbackIso001 F U V Z n HU etaU).inv ≫
    pullback.lift
      (relativeOpenChartParameterTripleToSecondOverlap001 F U V Z n HU HV etaU etaV).left
      ((relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU).left ≫
        (relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV).left)
      (relativeOpenChartParameterTriple_nativeTarget_square001 F U V Z n HU HV etaU etaV)

/-- Exact first target projection of the constructed native triple map. -/
theorem relativeOpenChartParameterNativeTripleMap_fst001 :
    relativeOpenChartParameterNativeTripleMap001 F U V Z n HU HV etaU etaV ≫
      pullback.fst (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left
        (relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV).left =
    (relativeOpenChartParameterTripleNativePullbackIso001 F U V Z n HU etaU).inv ≫
      (relativeOpenChartParameterTripleToSecondOverlap001 F U V Z n HU HV etaU etaV).left := by
  dsimp only [relativeOpenChartParameterNativeTripleMap001]
  rw [Category.assoc, pullback.lift_fst]

/-- The actual constructed triple map satisfies EXACTLY native GlueData's
t_fac projection, through the SAME original reciprocal transition. -/
theorem relativeOpenChartParameterNativeTripleMap_snd001 :
    relativeOpenChartParameterNativeTripleMap001 F U V Z n HU HV etaU etaV ≫
      pullback.snd (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left
        (relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV).left =
    pullback.fst (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
      (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left ≫
        (relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV).left := by
  dsimp only [relativeOpenChartParameterNativeTripleMap001]
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
    relativeOpenChartParameterTripleNativePullbackIso_inv_first001]

end PfaffianDescent
end
