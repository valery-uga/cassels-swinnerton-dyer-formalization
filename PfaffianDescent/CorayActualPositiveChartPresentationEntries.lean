import PfaffianDescent.CorayActualDegreeZeroChartPresentation
import PfaffianDescent.ProjectivePositiveTwist

/-! Actual positive-sheaf multiplication, in the OWN normalized Proj-chart
coordinates. No compatibility or equivalence is supplied by the caller.
SOURCE ONLY UNVERIFIED; root owns compiler and acceptance. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
open PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The SAME normalized chart coefficient, mapped into the point's OWN
degree-zero local ring, is the existing actual homogeneous local equation. -/
theorem actualAmbientChartCoefficient_atPrime
    (j : Fin 4) {d : ℕ} (p : A) (hp : p.IsHomogeneous d)
    (P : Ideal A) [P.IsPrime] (hj : X j ∈ P.primeCompl) :
    HomogeneousLocalization.mapId PS (Submonoid.powers_le.mpr hj)
        (ambientChartEvaluation j p) =
      localEquation PS P ⟨p, hp⟩ ⟨X j, isHomogeneous_X K j⟩ hj := by
  rw [ambientChartEvaluation_homogeneous j p hp]
  apply HomogeneousLocalization.val_injective
  rfl

/-- The actual categorical positive-twist stalk map has exactly the
normalized chart matrix entry in its existing positive local frames.
The sheaf multiplication, categorical stalk, evaluation, frame, and chart
local-ring map are all the original constructed maps. -/
theorem actualPositiveHomogeneousStalkMap_normalizedChartEntry
    (j : Fin 4) {d : ℕ} (p : A) (hp : p.IsHomogeneous d) (m : ℕ)
    (x : ProjectiveSpectrum.top PS)
    (hj : X j ∈ (positivePointIdeal PS x).primeCompl)
    (z : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (positiveModulePresheaf PS m).presheaf x)) :
    positiveStalkToFractionModule PS (m + d) x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (positiveMulHomogeneousPresheaf PS ⟨p, hp⟩ m) z) =
      positiveLocalTrivialization PS (positivePointIdeal PS x)
        ⟨X j, isHomogeneous_X K j⟩ hj (m + d)
        (HomogeneousLocalization.mapId PS (Submonoid.powers_le.mpr hj)
            (ambientChartEvaluation j p) *
          (positiveLocalTrivialization PS (positivePointIdeal PS x)
            ⟨X j, isHomogeneous_X K j⟩ hj m).symm
              (positiveStalkToFractionModule PS m x z)) := by
  let P := positivePointIdeal PS x
  let s : PS d := ⟨p, hp⟩
  let f : PS 1 := ⟨X j, isHomogeneous_X K j⟩
  let E := positiveLocalTrivialization PS P f hj m
  let E' := positiveLocalTrivialization PS P f hj (m + d)
  let r := E.symm (positiveStalkToFractionModule PS m x z)
  have hr : E r = positiveStalkToFractionModule PS m x z := E.apply_symm_apply _
  have hc := actualAmbientChartCoefficient_atPrime j p hp P hj
  calc
    _ = positiveMulHomogeneousStalk PS P s m
        (positiveStalkToFractionModule PS m x z) :=
      positiveStalkToFractionModule_stalkMap PS s m x z
    _ = positiveMulHomogeneousStalk PS P s m (E r) :=
      congrArg (positiveMulHomogeneousStalk PS P s m) hr.symm
    _ = E' (localEquation PS P s f hj * r) :=
      positiveMulHomogeneousStalk_localTrivialization_apply PS P s f hj m r
    _ = _ := congrArg (fun a : HomogeneousLocalization.AtPrime PS P => E' (a * r)) hc.symm

end PfaffianDescent.Coray
