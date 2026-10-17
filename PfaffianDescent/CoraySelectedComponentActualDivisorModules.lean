import PfaffianDescent.RegularPrincipalImmersionNativeRankOne
import PfaffianDescent.CoraySelectedComponentActualRegularPrincipalImmersion
import PfaffianDescent.SchemeModuleRankOneDualKernelIso

/-!
# Actual selected-component ideal, dual and native exact sequences

The ideal is the OWN canonical closed-immersion module. Its dual is the
OWN O-linear internal Hom. Actual regular equations supply rank-one unit
charts, canonical evaluation invertibility and tensor exactness internally.
This constructs no surface intersection pairing, adjunction or Hodge bound.
SOURCE ONLY / UNVERIFIED; root owns all compiler and audit checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Genuine divisor sheaf data on the SAME original smooth cubic, derived
from the actual selected minimal component. No ideal rank, invertibility,
duality, tensor exactness or Cartier statement is supplied as an input.
The final quotient is the literal tensor of i_*O_C with the OWN dual;
no unproved projection formula or normal-bundle identification is hidden. -/
theorem selectedProjectiveMinimalComponent_actualDivisorModuleData
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    letI : IsClosedImmersion i :=
      PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
    let L := IdealSheafDataModule.closedImmersionModule i
    let D := SchemeModuleInternalHom.dual L
    schemeModuleLocallyRankOne L ∧ schemeModuleLocallyRankOne D ∧
      IsIso (SchemeModuleInternalHom.dualEvaluation L) ∧
      (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).ShortExact ∧
      (closedImmersionIdealTwistSequence i D).ShortExact := by
  classical
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let L := IdealSheafDataModule.closedImmersionModule i
  let D := SchemeModuleInternalHom.dual L
  let H : PfaffianDescent.RegularPrincipalImmersion i :=
    selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
      p q hp hp0 n hq hnot C hCmin
  have hL : schemeModuleLocallyRankOne L := H.inverseCartierTwist_locallyRankOne
  have hD : schemeModuleLocallyRankOne D := schemeModuleLocallyRankOne_dual L hL
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts L hL
  have hevaluation : IsIso (SchemeModuleInternalHom.dualEvaluation L) :=
    SchemeModuleInternalHom.dualEvaluation_isIso_of_pointwise_unitCharts L B hB eB
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  exact ⟨hL, hD, hevaluation, hS,
    schemeModuleLocallyRankOne_tensor_shortExact D hD
      (IdealSheafDataModule.closedImmersionModulePushforwardSequence i) hS⟩

end PfaffianDescent.Coray
