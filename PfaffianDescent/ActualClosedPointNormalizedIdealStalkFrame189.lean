import PfaffianDescent.ActualDVRNormalizedResidueParameter186
import PfaffianDescent.CorayNormalizationClosedPointIdealStalk

/-! Actual normalized frame of the SAME closed-point ideal stalk.
The generic original scheme is not replaced by its normalization. The
second theorem constructs the parameter and ideal frame together, retaining
the original residue map, differential basis and original ideal inclusion.
SOURCE ONLY; root owns compiler checks. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open IdealSheafDataModule IsLocalRing KaehlerDifferential
open scoped TensorProduct
universe u

/-- A genuine parameter of the original local ring constructs a frame of
the actual original point ideal, with its actual inclusion value preserved.
This intermediate uses only ordinary local-ring parameter data. -/
theorem closedPointIdeal_exists_stalkFrame_of_parameter189
    (X : Scheme.{u}) (P : closedPoints X)
    [IsDomain (X.presheaf.stalk P.1)]
    (t : X.presheaf.stalk P.1) (ht : t ≠ 0)
    (hspan : maximalIdeal (X.presheaf.stalk P.1) =
      Ideal.span ({t} : Set (X.presheaf.stalk P.1))) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    letI := schemeModuleStalkModule M P.1
    ∃ e : X.presheaf.stalk P.1 ≃ₗ[X.presheaf.stalk P.1] M.presheaf.stalk P.1,
      ∀ r, closedImmersionModuleStalkToRingLinearMap i P.1 (e r) = r * t := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let R := X.presheaf.stalk P.1
  let M := (show X.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule M P.1
  let j := closedImmersionModuleStalkToRingLinearMap i P.1
  let E : M.presheaf.stalk P.1 ≃ₗ[R] maximalIdeal R :=
    Coray.closedPointIdeal_stalkLinearEquivMaximalIdeal X P
  let E' : M.presheaf.stalk P.1 ≃ₗ[R] Ideal.span ({t} : Set R) :=
    E.trans (LinearEquiv.ofEq _ _ hspan)
  have hE (m : M.presheaf.stalk P.1) : (E' m : R) = j m := by
    change (E m : R) = j m
    exact Coray.closedPointIdeal_stalkLinearEquivMaximalIdeal_apply X P m
  have hEinv (s : Ideal.span ({t} : Set R)) : j (E'.symm s) = s.1 := by
    rw [← hE, E'.apply_symm_apply]
  let A : R ≃ₗ[R] Ideal.span ({t} : Set R) :=
    LinearEquiv.toSpanNonzeroSingleton R R t ht
  refine ⟨A.trans E'.symm, ?_⟩
  intro r
  change j (E'.symm (A r)) = r * t
  rw [hEinv]
  rfl

/-- The actual one-vector Kaehler basis and separable original residue
construct the normalized parameter and frame of the SAME point ideal.
No parameter, ideal-generator, frame or inclusion-comparison premise is
supplied. The original curve's chart/stalk basis assembly is separate. -/
theorem actualClosedPoint_exists_normalizedIdealStalkFrame189
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
    let M := (show X.Modules from closedImmersionModule i)
    letI := schemeModuleStalkModule M P.1
    ∃ t : R, residue R t = 0 ∧ maximalIdeal R = Ideal.span ({t} : Set R) ∧
      (1 ⊗ₜ[R] KaehlerDifferential.D k R t :
        (ResidueField R) ⊗[R] KaehlerDifferential k R) = 1 ⊗ₜ[R] b () ∧
      ∃ e : R ≃ₗ[R] M.presheaf.stalk P.1,
        ∀ r, closedImmersionModuleStalkToRingLinearMap i P.1 (e r) = r * t := by
  let R := X.presheaf.stalk P.1
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule M P.1
  obtain ⟨t, ht, hspan, hd⟩ :=
    dvrKaehlerResidueBasis_exists_normalizedUniformizer186 (k := k) (R := R) b
  have ht0 : t ≠ 0 := by
    intro hzero
    obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hpimem : pi ∈ maximalIdeal R := by
      rw [hpi.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self pi
    rw [hspan, hzero] at hpimem
    exact hpi.ne_zero (by simpa using hpimem)
  obtain ⟨e, he⟩ := closedPointIdeal_exists_stalkFrame_of_parameter189 X P t ht0 hspan
  exact ⟨t, ht, hspan, hd, e, he⟩

end PfaffianDescent
