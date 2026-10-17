import PfaffianDescent.ActualClosedPointWholeDualCokernelPrincipal194
import PfaffianDescent.ActualClosedPointNormalizedIdealStalkFrame189
import Mathlib.AlgebraicGeometry.FunctionField

/-! SOURCE ONLY200. Omega-free factory of the SAME original point ideal,
whole global dual increment, its native projection, and entire stalk complex.
Original geometry constructs every parameter/frame/cokernel identification. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing
open scoped nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem actualClosedPoint_exists_regularWholeDualCokernelPrincipal200
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let R := X.presheaf.stalk P.1
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let F := schemeModuleStalkModuleFunctor X P.1
    let S := incrementCokernelSequence (closedImmersionModuleToUnit i)
    S.ShortExact ∧
    ∃ (t : R) (e₀ : R ≃ₗ[R] F.obj M),
      t ∈ R⁰ ∧ maximalIdeal R = Ideal.span ({t} : Set R) ∧
      (∀ r, closedImmersionModuleStalkToRingLinearMap i P.1 (e₀ r) = r * t) ∧
      ∃ (U : X.Opens) (hPU : P.1 ∈ U)
        (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U),
        let d := actualDualIncrementStalkCoefficientIso194 U ⟨P.1, hPU⟩ M e e₀
        ∃ q : (S.map F).X₃ ≅ (pointCartierYonedaCoefficientComplex t).X₃,
          (S.map F).g ≫ q.hom = d.hom ≫ (pointCartierYonedaCoefficientComplex t).g ∧
          ∃ a : S.map F ≅ pointCartierYonedaCoefficientComplex t,
            a.hom.τ₁ = (schemeModuleUnitStalkIso X P.1).hom ∧
            a.hom.τ₂ = d.hom ∧ a.hom.τ₃ = q.hom := by
  dsimp only
  let R := X.presheaf.stalk P.1
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let F := schemeModuleStalkModuleFunctor X P.1
  let j := closedImmersionModuleToUnit i
  let S := incrementCokernelSequence j
  letI := schemeModuleStalkModule M P.1
  have hS : S.ShortExact := actualClosedPointDualIncrement_shortExact194 X P
  refine ⟨hS, ?_⟩
  obtain ⟨t, ht, hrange⟩ := Coray.closedPointIdeal_stalk_exists_regularGenerator_of_isDVR X P
  have hspan : maximalIdeal R = Ideal.span ({t} : Set R) :=
    (Coray.closedPointIdeal_stalk_range_eq_maximalIdeal X P).symm.trans hrange
  obtain ⟨e₀, he₀⟩ := closedPointIdeal_exists_stalkFrame_of_parameter189 X P t
    (isRegular_iff_ne_zero.mp ht) hspan
  have he : ∀ r, schemeModuleStalkToRingLinearMap j P.1 (e₀ r) = r * t := by
    intro r
    exact he₀ r
  have hM : schemeModuleLocallyRankOne M :=
    Coray.closedPointIdeal_locallyRankOne_of_stalk_isDVR X P
  obtain ⟨U, hPU, ⟨e⟩⟩ := hM P.1
  let x : U := ⟨P.1, hPU⟩
  have hreg : t ∈ R⁰ := actualDualIncrementStalk_parameter_regular194 U x M e j hS e₀ t he
  let q := actualDualIncrementWholeStalkCokernelIso194 U x M e j hS e₀ t he
  let a := actualDualIncrementWholeStalkPrincipalIso194 U x M e j hS e₀ t he
  refine ⟨t, e₀, hreg, hspan, he₀, U, hPU, e, q, ?_, a, ?_, ?_, ?_⟩
  · exact actualDualIncrementWholeStalkCokernelIso_projection194 U x M e j hS e₀ t he
  · rfl
  · rfl
  · rfl

end PfaffianDescent
