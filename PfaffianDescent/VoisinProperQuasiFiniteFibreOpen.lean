import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import AllCharacteristics.ProjectiveConfigurationGenericSpecialization
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Quasi-finite fibres form an open locus for a proper family

The non-quasi-finite locus in the source is closed because quasi-finiteness
at a source point is open. Properness makes its image closed in the parameter
scheme. Thus one parameter with a wholly quasi-finite fibre makes the
generic fibre quasi-finite when the parameter scheme is integral.
-/

namespace PfaffianDescent

open AlgebraicGeometry TopologicalSpace CategoryTheory

universe u

/-- Parameter values over which every source point is quasi-finite. -/
def quasiFiniteFibreLocus {X Y : Scheme.{u}} (f : X ⟶ Y) : Set Y :=
  {y | ∀ x : X, f x = y → f.QuasiFiniteAt x}

theorem isOpen_quasiFiniteFibreLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsOpen (quasiFiniteFibreLocus f) := by
  let B : Set X := {x | ¬ f.QuasiFiniteAt x}
  have hB : IsClosed B := f.isOpen_quasiFiniteAt.isClosed_compl
  have hImage : IsClosed (f '' B) := f.isClosedMap B hB
  have hEq : quasiFiniteFibreLocus f = (f '' B)ᶜ := by
    ext y
    simp only [quasiFiniteFibreLocus, B,
      Set.mem_compl_iff, Set.mem_image, not_exists]
    constructor
    · intro hy x hx
      exact hx.1 (hy x hx.2)
    · intro hy x hxy
      by_contra hx
      exact hy x ⟨hx, hxy⟩
  rw [hEq]
  exact hImage.isOpen_compl

/-- One wholly quasi-finite fibre of a proper family forces the generic
fibre to be quasi-finite over an integral parameter scheme. -/
theorem quasiFiniteAt_over_genericPoint_of_exists_good_fibre
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsIntegral Y]
    (y : Y) (hy : y ∈ quasiFiniteFibreLocus f) :
    ∀ x : X, f x = genericPoint Y → f.QuasiFiniteAt x := by
  let B : Set Y := (quasiFiniteFibreLocus f)ᶜ
  have hclosed : IsClosed B := (isOpen_quasiFiniteFibreLocus f).isClosed_compl
  have hproper : B ≠ Set.univ := by
    intro h
    have hyB : y ∈ B := by rw [h]; trivial
    exact hyB hy
  have hgeneric : genericPoint Y ∉ B :=
    AllCharacteristics.genericPoint_avoids_proper_closed_of_isIntegral
      Y hclosed hproper
  intro x hx
  have hη : genericPoint Y ∈ quasiFiniteFibreLocus f := by
    simpa only [B, Set.mem_compl_iff, not_not] using hgeneric
  exact hη x hx

/-- A single finite fibre of a proper family over an integral parameter
scheme yields a finite morphism after restricting to an open neighborhood
of the generic point. The existence of the finite neighborhood is Mathlib's
proper-plus-finite-fibre theorem; integrality puts the generic point in it. -/
theorem exists_genericPoint_finite_restriction_of_one_finite_fibre
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsIntegral Y]
    (y : Y) (hy : (f ⁻¹' {y}).Finite) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧ IsFinite (f ∣_ V) := by
  obtain ⟨V, hyV, hfin⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton
      (f := f) y hy
  have hηV : genericPoint Y ∈ V :=
    (genericPoint_specializes y).mem_open V.isOpen hyV
  exact ⟨V, hηV, hfin⟩

/-- A proper scheme over a field with only finitely many closed points is
finite over that field. The Jacobson property turns the finite closed-point
set into a discrete finite underlying space; quasi-finiteness then follows
from the finite-fibre criterion. -/
theorem isFinite_of_proper_over_field_of_finite_closedPoints
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (hclosed : (closedPoints X).Finite) : IsFinite f := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  haveI : DiscreteTopology X := JacobsonSpace.discreteTopology hclosed
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : Finite X := finite_of_compact_of_discrete
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (fun _ ↦ Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- Over an algebraically closed field, finiteness of the set of actual
field-valued points of a proper scheme already implies a finite morphism.
This uses the closed-point equivalence rather than a reducedness assumption. -/
theorem isFinite_of_proper_over_algClosed_of_finite_fieldPoints
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (hpoints : Finite {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _}) :
    IsFinite f := by
  haveI : Finite {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} := hpoints
  haveI : Finite (closedPoints X) :=
    Finite.of_equiv _ (pointEquivClosedPoint f)
  have hclosed : (closedPoints X).Finite := Set.toFinite _
  exact isFinite_of_proper_over_field_of_finite_closedPoints f hclosed

end PfaffianDescent
