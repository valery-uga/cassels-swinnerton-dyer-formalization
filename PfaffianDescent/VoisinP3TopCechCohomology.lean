import PfaffianDescent.VoisinP3TopCechCoordinateRealization

/-!
# The explicit top Cech cohomology of `O(-6)` on `P³`

The raw degree-three cocycles are quotiented by the actual image of the
degree-two Cech differential.  The quadratic residue coordinates have
exactly that boundary subgroup as kernel and are jointly surjective.  Hence
they identify the resulting top Cech cohomology group with the ten
coordinates indexed by quadratic monomials.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentCechExact

variable (K : Type u) [Field K]

/-- Raw top cocycles of the four-chart Cech complex for `O(-6)`. -/
def p3NegativeSixTopCocycles : AddSubgroup
    ((p3NegativeTwistCechComplex (K := K) 6).X 3) :=
  AddMonoidHom.ker
    ((p3NegativeTwistCechComplex (K := K) 6).d 3 4).hom

/-- The preceding Cech differential, with codomain restricted to top
cocycles by `d² = 0`. -/
def p3NegativeSixBoundaryToCocycles :
    (p3NegativeTwistCechComplex (K := K) 6).X 2 →+
      p3NegativeSixTopCocycles K where
  toFun z := ⟨(p3NegativeTwistCechComplex (K := K) 6).d 2 3 z, by
    change (p3NegativeTwistCechComplex (K := K) 6).d 3 4
      ((p3NegativeTwistCechComplex (K := K) 6).d 2 3 z) = 0
    exact ConcreteCategory.congr_hom
      ((p3NegativeTwistCechComplex (K := K) 6).d_comp_d 2 3 4) z⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp

/-- All quadratic residue coordinates, evaluated on a raw top cocycle. -/
def p3NegativeSixTopResidueCoordinates :
    p3NegativeSixTopCocycles K →+
      (P3QuadraticExponent → K) where
  toFun w b := p3NegativeSixRawResidue K b w.1
  map_zero' := by
    funext b
    simp [p3NegativeSixRawResidue]
  map_add' x y := by
    funext b
    simp [p3NegativeSixRawResidue]

@[simp]
lemma p3NegativeSixTopResidueCoordinates_apply
    (w : p3NegativeSixTopCocycles K) (b : P3QuadraticExponent) :
    p3NegativeSixTopResidueCoordinates K w b =
      p3NegativeSixRawResidue K b w.1 := rfl

/-- The kernel of the joint residue map consists exactly of genuine
degree-two Cech boundaries. -/
theorem mem_p3NegativeSixTopResidueCoordinates_ker_iff_boundary
    (w : p3NegativeSixTopCocycles K) :
    w ∈ (p3NegativeSixTopResidueCoordinates K).ker ↔
      ∃ z : (p3NegativeTwistCechComplex (K := K) 6).X 2,
        (p3NegativeTwistCechComplex (K := K) 6).d 2 3 z = w.1 := by
  constructor
  · intro hw
    have hcoord : p3NegativeSixTopResidueCoordinates K w = 0 := hw
    apply p3NegativeSixRawCocycle_is_boundary_of_residue_zero K w.1 w.property
    intro b hb
    have h := congrFun hcoord (⟨b, hb⟩ : P3QuadraticExponent)
    simpa using h
  · rintro ⟨z, hz⟩
    change p3NegativeSixTopResidueCoordinates K w = 0
    funext b
    rw [p3NegativeSixTopResidueCoordinates_apply, ← hz]
    exact p3NegativeSixRawResidue_boundary_eq_zero K z b

/-- The residue kernel is literally the range of the preceding Cech
differential restricted to cocycles. -/
theorem p3NegativeSixTopResidueCoordinates_ker_eq_boundary_range :
    (p3NegativeSixTopResidueCoordinates K).ker =
      (p3NegativeSixBoundaryToCocycles K).range := by
  ext w
  rw [mem_p3NegativeSixTopResidueCoordinates_ker_iff_boundary]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩

/-- The joint quadratic residue map is surjective on raw top cocycles. -/
theorem p3NegativeSixTopResidueCoordinates_surjective :
    Function.Surjective (p3NegativeSixTopResidueCoordinates K) := by
  intro c
  obtain ⟨w, hwcycle, hwres⟩ :=
    p3NegativeSixRawResidue_surjective_on_cocycles K c
  refine ⟨⟨w, hwcycle⟩, ?_⟩
  funext b
  exact hwres b

/-- Explicit additive description of top Cech cohomology: cocycles modulo
the residue kernel (proved above to be exactly the boundary range) are the
ten quadratic monomial coordinates. -/
noncomputable def p3NegativeSixTopCechCohomologyResidueEquiv :
    p3NegativeSixTopCocycles K ⧸
        (p3NegativeSixTopResidueCoordinates K).ker ≃+
      (P3QuadraticExponent → K) :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (p3NegativeSixTopResidueCoordinates K)
    (p3NegativeSixTopResidueCoordinates_surjective K)

end PfaffianDescent.ProjectiveNegativeTwist
