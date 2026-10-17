import PfaffianDescent.CoraySignedCycleWordDegreeSelection
import AllCharacteristics.EffectiveCycleToZeroCycle

/-! Actual effective cycles and integer coefficients construct actual signed
point operations. Original multiplicities and FULL pi residue degrees remain
literal. The imported cycle encoding is pending historical001, not accepted.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The SAME actual integer combination of the SAME actual effective cycles
is represented by literal positive-dual/negative-ideal point operations. No
operation word or desired weight is input. Repeated points retain their
actual integer coefficients, even when the two supports intersect. -/
theorem effectiveCycles_integerCombination_exists_signedPointTensorOperations
    (pi : X ⟶ Spec (CommRingCat.of K)) (zD zH : EffectiveZeroCycle X) (a b : ℤ) :
    ∃ ops : List (closedPoints X × Bool),
      signedPointTensorOperationsZeroCycle ops = a • zD.toZeroCycle + b • zH.toZeroCycle ∧
        schemeModuleSignedClosedPointTensorWeightSum pi ops =
          a * (EffectiveZeroCycle.degree pi zD : ℤ) +
            b * (EffectiveZeroCycle.degree pi zH : ℤ) := by
  obtain ⟨ops, hcycle, hweight⟩ := zeroCycle_exists_signedPointTensorOperations pi
    (a • zD.toZeroCycle + b • zH.toZeroCycle)
  refine ⟨ops, hcycle, ?_⟩
  rw [hweight, map_add, map_smul, map_smul,
    EffectiveZeroCycle.degree_toZeroCycle, EffectiveZeroCycle.degree_toZeroCycle]
  simp only [smul_eq_mul]

end PfaffianDescent.Coray
