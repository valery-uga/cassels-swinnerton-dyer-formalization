import PfaffianDescent.SchemeModuleActualDualIncrementStalkPrincipal194
import PfaffianDescent.ActualClosedPointNormalizedDualPrincipalSequence190

/-! SOURCE ONLY194. The SAME original point ideal's whole global canonical
cokernel is retained. Its exactness, parameter, frame, native cokernel Iso
and projection square are internally constructed from ordinary point geometry. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing KaehlerDifferential
open scoped TensorProduct nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original I_P geometry gives genuine exactness of the literal whole
canonical increment, using actual original pointwise ideal charts. -/
theorem actualClosedPointDualIncrement_shortExact194
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  have hM : schemeModuleLocallyRankOne M :=
    Coray.closedPointIdeal_locallyRankOne_of_stalk_isDVR X P
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  letI : Mono (closedImmersionModuleToUnit i) := by
    change Mono (idealModuleToUnit i.ker)
    infer_instance
  exact incrementCokernelSequence_shortExact_of_pointwise_unitCharts
    (closedImmersionModuleToUnit i) B hB eB

/-- The normalized original differential basis constructs the whole actual
sheaf quotient's principal stalk presentation, preserving its native projection.
There is no frame, exactness, residue coefficient or sequence-comparison premise. -/
theorem actualClosedPoint_exists_normalizedWholeDualCokernelPrincipal194
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) {k : Type u} [Field k]
    [IsDomain (X.presheaf.stalk P.1)]
    [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    [Algebra k (X.presheaf.stalk P.1)]
    [Algebra k (ResidueField (X.presheaf.stalk P.1))]
    [IsScalarTower k (X.presheaf.stalk P.1) (ResidueField (X.presheaf.stalk P.1))]
    [Algebra.IsSeparable k (ResidueField (X.presheaf.stalk P.1))]
    (b : Module.Basis Unit (X.presheaf.stalk P.1)
      (KaehlerDifferential k (X.presheaf.stalk P.1))) :
    let R := X.presheaf.stalk P.1
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let F := schemeModuleStalkModuleFunctor X P.1
    let S := incrementCokernelSequence (closedImmersionModuleToUnit i)
    ∃ (t : R) (e₀ : R ≃ₗ[R] F.obj M),
      residue R t = 0 ∧ maximalIdeal R = Ideal.span ({t} : Set R) ∧
      (1 ⊗ₜ[R] KaehlerDifferential.D k R t :
        (ResidueField R) ⊗[R] KaehlerDifferential k R) = 1 ⊗ₜ[R] b () ∧
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
  obtain ⟨t, e₀, ht, hspan, hd, he₀, _hreg, _hcoord, _hexact, _hiso⟩ :=
    actualClosedPoint_exists_normalizedDualPrincipalSequence190 X P b
  have he : ∀ r, schemeModuleStalkToRingLinearMap j P.1 (e₀ r) = r * t := by
    intro r
    exact he₀ r
  have hM : schemeModuleLocallyRankOne M :=
    Coray.closedPointIdeal_locallyRankOne_of_stalk_isDVR X P
  obtain ⟨U, hPU, ⟨e⟩⟩ := hM P.1
  let x : U := ⟨P.1, hPU⟩
  have hS : S.ShortExact := actualClosedPointDualIncrement_shortExact194 X P
  let q := actualDualIncrementWholeStalkCokernelIso194 U x M e j hS e₀ t he
  let a := actualDualIncrementWholeStalkPrincipalIso194 U x M e j hS e₀ t he
  refine ⟨t, e₀, ht, hspan, hd, U, hPU, e, q, ?_, a, ?_, ?_, ?_⟩
  · exact actualDualIncrementWholeStalkCokernelIso_projection194 U x M e j hS e₀ t he
  · rfl
  · rfl
  · rfl

end PfaffianDescent
