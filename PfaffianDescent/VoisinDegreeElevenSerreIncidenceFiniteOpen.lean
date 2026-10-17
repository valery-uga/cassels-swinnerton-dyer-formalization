import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen
import PfaffianDescent.VoisinGenericTripleFinite

/-! # Finite-zero opens carried by an actual section-incidence projection

The zero family and incidence projection are actual scheme morphisms.  An
open incidence projection carries the finite-zero open to an open of the
configuration base.  A single finite-zero witness puts its generic point in
that image.  This statement does not construct the section-kernel family or
assert that its projection is open.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual configuration locus reached by parameters with finite zero. -/
def serreIncidenceFiniteZeroImage {Z I B : Scheme.{u}}
    (zero : Z ⟶ I) [IsProper zero] (π : I ⟶ B) : Set B :=
  π '' (cubicClosedPointSerreFiniteZeroResidual_goodOpen zero : Set I)

theorem serreIncidenceFiniteZeroImage_isOpen {Z I B : Scheme.{u}}
    (zero : Z ⟶ I) [IsProper zero] (π : I ⟶ B)
    (hπ : IsOpenMap π) : IsOpen (serreIncidenceFiniteZeroImage zero π) :=
  hπ _ (cubicClosedPointSerreFiniteZeroResidual_goodOpen zero).isOpen

/-- An actual finite-zero parameter gives a parameter above the generic
configuration whose zero family is finite on a neighbourhood. -/
theorem serreIncidenceFiniteZeroImage_genericPoint {Z I B : Scheme.{u}}
    (zero : Z ⟶ I) [IsProper zero] (π : I ⟶ B) [IsIntegral B]
    (hπ : IsOpenMap π) (i : I) (hi : (zero ⁻¹' {i}).Finite) :
    ∃ j : I, π j = genericPoint B ∧
      j ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen zero := by
  have hiV := cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre
    zero i hi
  have hη : genericPoint B ∈ serreIncidenceFiniteZeroImage zero π :=
    (genericPoint_specializes (π i)).mem_open
      (serreIncidenceFiniteZeroImage_isOpen zero π hπ) ⟨i, hiV, rfl⟩
  obtain ⟨j, hj, hπj⟩ := hη
  exact ⟨j, hπj, hj⟩

/-- A literal field-valued incidence parameter in the finite-zero open has
an actual finite zero scheme after pullback. -/
theorem serreIncidenceFiniteZero_fieldPoint {Z I : Scheme.{u}}
    (zero : Z ⟶ I) [IsProper zero] {F : Type u} [Field F]
    (s : Spec (.of F) ⟶ I)
    (hs : s (IsLocalRing.closedPoint F) ∈
      cubicClosedPointSerreFiniteZeroResidual_goodOpen zero) :
    IsFinite (CategoryTheory.Limits.pullback.snd zero s) := by
  let V := cubicClosedPointSerreFiniteZeroResidual_goodOpen zero
  letI : IsFinite (zero ∣_ V) :=
    cubicClosedPointSerreFiniteZeroResidual_goodOpen_finite zero
  have hrange : Set.range s ⊆ Set.range V.ι := by
    rintro y ⟨x, rfl⟩
    rw [V.range_ι]
    have hx : x = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    rw [hx]
    change s (IsLocalRing.closedPoint F) ∈
      cubicClosedPointSerreFiniteZeroResidual_goodOpen zero
    exact hs
  let sV := IsOpenImmersion.lift V.ι s hrange
  have hfac : sV ≫ V.ι = s := IsOpenImmersion.lift_fac _ _ _
  rw [← hfac]
  exact finite_pullback_of_factor_through_finite_open zero V sV

end PfaffianDescent
