import PfaffianDescent.FiniteFlatHilbertNoetherianDatum279
import PfaffianDescent.NativeOpenContainedFiniteFlatPointEquiv315
import AllCharacteristics.ClosedPointFiniteSubscheme

/-! Actual closed points give whole finite-flat Hilbert points and their
chart seeds, using only membership of the original point in the open. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  (F : X ⟶ Spec (.of K)) [LocallyOfFiniteType F] (P : closedPoints X)

def nativeClosedPointHilbertSeed317 : FiniteFlatHilbertPoint195 F (F.residueDegree P.val) :=
  finiteSubschemeDatumToHilbertPoint279 F (F.residueDegree P.val)
    (AllCharacteristics.finiteSubschemeDatumOfClosedPoint F P)

lemma nativeClosedPointHilbertSeed_ideal317 :
    (nativeClosedPointHilbertSeed317 F P).val = (X.fromSpecResidueField P.val).ker :=
  AllCharacteristics.finiteSubschemeDatumOfClosedPoint_ideal F P

lemma nativeClosedPointHilbertSeed_range317 :
    Set.range (nativeClosedPointHilbertSeed317 F P).val.subschemeι = {P.val} := by
  letI : IsClosedImmersion (X.fromSpecResidueField P.val) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.property
  rw [Scheme.IdealSheafData.range_subschemeι, nativeClosedPointHilbertSeed_ideal317,
    Scheme.Hom.support_ker]
  simpa only [TopologicalSpace.Closeds.coe_closure, Scheme.range_fromSpecResidueField] using
    P.property.closure_eq

variable (j : Y ⟶ X) [IsOpenImmersion j] (hP : P.val ∈ Set.range j)

include hP in
private lemma nativeClosedPointHilbertSeed_inOpen317 :
    Set.range (nativeClosedPointHilbertSeed317 F P).val.subschemeι ⊆ Set.range j := by
  rw [nativeClosedPointHilbertSeed_range317]
  exact Set.singleton_subset_iff.mpr hP

def nativeClosedPointOpenHilbertSeed317 :
    FiniteFlatHilbertPoint195 (j ≫ F) (F.residueDegree P.val) :=
  nativeOpenContainedFiniteFlatPointLift315 j F (F.residueDegree P.val)
    (nativeClosedPointHilbertSeed317 F P) (nativeClosedPointHilbertSeed_inOpen317 F P j hP)

lemma nativeClosedPointOpenHilbertSeed_ideal317 :
    (nativeClosedPointOpenHilbertSeed317 F P j hP).val =
      (X.fromSpecResidueField P.val).ker.comap j :=
  (nativeOpenContainedFiniteFlatPointLift_comap315 j F (F.residueDegree P.val)
    (nativeClosedPointHilbertSeed317 F P) (nativeClosedPointHilbertSeed_inOpen317 F P j hP)).trans
      (congrArg (fun I : X.IdealSheafData => I.comap j) (nativeClosedPointHilbertSeed_ideal317 F P))

end PfaffianDescent
end
