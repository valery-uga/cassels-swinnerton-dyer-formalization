import PfaffianDescent.ActualClosedPointNormalizedIdealStalkFrame189
import PfaffianDescent.ActualIdealStalkDualPrincipalSequence190

/-! SOURCE ONLY / UNCHECKED. Same ORIGINAL X/P/I_P and scalar action.
The ideal frame, normalized parameter, dual coordinate and entire principal
increment are all internally derived from the actual Kaehler basis. This
uses the LINEAR dual of the actual ideal stalk; the actual sheaf-dual stalk
comparison is a separate additive module. No trace/nonzero-boundary input. -/
noncomputable section
set_option autoImplicit false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing KaehlerDifferential
open IdealSheafDataModule
open scoped TensorProduct nonZeroDivisors
universe u

/-- Ordinary original point geometry constructs the normalized principal
dual sequence with its true inclusion coefficient; no frame or scalar
normalization conclusion is supplied as a premise. -/
theorem actualClosedPoint_exists_normalizedDualPrincipalSequence190
    (X : Scheme.{u}) (P : closedPoints X) {k : Type u} [Field k]
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
    let I := (show X.Modules from closedImmersionModule i)
    letI := schemeModuleStalkModule I P.1
    let j := closedImmersionModuleStalkToRingLinearMap i P.1
    ∃ (t : R) (e : R ≃ₗ[R] I.presheaf.stalk P.1),
      residue R t = 0 ∧ maximalIdeal R = Ideal.span ({t} : Set R) ∧
      (1 ⊗ₜ[R] KaehlerDifferential.D k R t :
        (ResidueField R) ⊗[R] KaehlerDifferential k R) = 1 ⊗ₜ[R] b () ∧
      ∃ he : ∀ r, j (e r) = r * t,
        t ∈ R⁰ ∧ actualIdealFrameDualCoordinate190 e j = t ∧
        (actualIdealFrameDualIncrement190 e j t he).ShortExact ∧
        Nonempty (actualIdealFrameDualIncrement190 e j t he ≅
          pointCartierYonedaCoefficientComplex t) := by
  let R := X.presheaf.stalk P.1
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let I := (show X.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule I P.1
  let j := closedImmersionModuleStalkToRingLinearMap i P.1
  obtain ⟨t, ht, hspan, hd, e, he⟩ :=
    actualClosedPoint_exists_normalizedIdealStalkFrame189 X P b
  have ht0 : t ≠ 0 := by
    intro hz
    obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hpimem : pi ∈ maximalIdeal R := by
      rw [hpi.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self pi
    rw [hspan, hz] at hpimem
    exact hpi.ne_zero (by simpa using hpimem)
  have hreg : t ∈ R⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr ht0
  exact ⟨t, e, ht, hspan, hd, he, hreg,
    actualIdealFrameDualCoordinate_inclusion190 e j t he,
    actualIdealFrameDualIncrement_shortExact190 e j t he hreg,
    ⟨actualIdealFrameDualIncrementPrincipalIso190 e j t he⟩⟩

end PfaffianDescent
