import PfaffianDescent.VoisinProperQuasiFiniteFibreOpen
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # The actual finite-fibre open of a proper pencil -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The maximal parameter open on which a proper pencil is finite. -/
def cubicClosedPointSerreFiniteZeroResidual_goodOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : Y.Opens :=
  ⟨quasiFiniteFibreLocus f, isOpen_quasiFiniteFibreLocus f⟩

theorem cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y)
    (hy : (f ⁻¹' {y}).Finite) :
    y ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen f := by
  rintro x rfl
  have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr hy
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem cubicClosedPointSerreFiniteZeroResidual_goodOpen_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsFinite (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f) := by
  let V := cubicClosedPointSerreFiniteZeroResidual_goodOpen f
  suffices LocallyQuasiFinite (f ∣_ V) from .of_isProper_of_locallyQuasiFinite _
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  ext x
  have h : f.QuasiFiniteAt ((f ⁻¹ᵁ V).ι x) := x.2 _ rfl
  rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι,
    Scheme.Hom.quasiFiniteAt_comp_iff] at h
  simpa using h

/-- Two finite endpoints belong to the same actual finite parameter open. -/
theorem cubicClosedPointSerreFiniteZeroResidual_goodOpen_contains_endpoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y₀ y₁ : Y)
    (h₀ : (f ⁻¹' {y₀}).Finite) (h₁ : (f ⁻¹' {y₁}).Finite) :
    y₀ ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen f ∧
      y₁ ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen f ∧
      IsFinite (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f) :=
  ⟨cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre f y₀ h₀,
    cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre f y₁ h₁,
    cubicClosedPointSerreFiniteZeroResidual_goodOpen_finite f⟩

/-- Flatness on the actual finite open suffices for equality of endpoint lengths.
The rest of the proper pencil need not have finite fibres. -/
theorem cubicClosedPointSerreFiniteZeroResidual_goodOpen_finrank_endpoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsIntegral Y]
    (y₀ y₁ : Y) (h₀ : (f ⁻¹' {y₀}).Finite) (h₁ : (f ⁻¹' {y₁}).Finite)
    [Flat (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f)]
    [LocallyOfFinitePresentation (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f)] :
    (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f).finrank
      ⟨y₀, cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre f y₀ h₀⟩ =
    (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f).finrank
      ⟨y₁, cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre f y₁ h₁⟩ := by
  let V := cubicClosedPointSerreFiniteZeroResidual_goodOpen f
  letI : Nonempty V := ⟨⟨y₀,
    cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre f y₀ h₀⟩⟩
  letI : IsFinite (f ∣_ V) := cubicClosedPointSerreFiniteZeroResidual_goodOpen_finite f
  exact (Scheme.Hom.isLocallyConstant_finrank (f ∣_ V)).apply_eq_of_preconnectedSpace _ _

end PfaffianDescent
