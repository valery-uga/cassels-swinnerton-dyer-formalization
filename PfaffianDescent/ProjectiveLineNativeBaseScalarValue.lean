import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.SchemeAffineFunctions
import AllCharacteristics.HomogeneousProjectiveAmbient
import PfaffianDescent.ProjectiveStructureZeroScalarValue
/-! SOURCE ONLY / UNCHECKED. Literal original quotient Bool P1 structure map
and its coefficient pullback values, without defining a scalar action by
transport or assuming global-function normalization. -/
noncomputable section
namespace PfaffianDescent.ProjectiveLineNative
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "P" => MvPolynomial.homogeneousSubmodule Bool K
local notation "L" => (⊥ : HomogeneousIdeal P)
local notation "PS" => AllCharacteristics.HomogeneousProjective.grading L
/-- The standard projective-space structure map to the ground field. -/
noncomputable def actualLineQuotientBaseMap : Proj PS ⟶ Spec (.of K) :=
  Proj.toSpecZero PS ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (PS 0)))

/-- The actual structure morphism sends a ground-field scalar to the same
fraction `C c / 1` at every projective point. -/
theorem actualLineQuotientBaseMap_scalar_value
    (c : K) (x : ProjectiveSpectrum.top PS) :
    ((affineFunctionHom (actualLineQuotientBaseMap K) c).1 ⟨x, trivial⟩).val =
      Localization.mk (algebraMap K (AllCharacteristics.HomogeneousProjective.CoordinateRing L) c : AllCharacteristics.HomogeneousProjective.CoordinateRing L)
        (1 : (pointIdeal PS x).primeCompl) := by
  have hbase : affineFunctionHom (actualLineQuotientBaseMap K) c =
      affineFunctionHom (Proj.toSpecZero PS) (algebraMap K (PS 0) c) := by
    exact congrArg (fun f => f c)
      (affineFunctionHom_comp_Spec (Proj.toSpecZero PS) (algebraMap K (PS 0)))
  rw [hbase]
  exact ProjectiveStructureNative.projectiveStructureZero_value PS
    (algebraMap K (PS 0) c) x

end PfaffianDescent.ProjectiveLineNative
end
