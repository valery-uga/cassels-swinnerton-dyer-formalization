import AllCharacteristics.UniversalSmoothParameters
import AllCharacteristics.HypersurfaceSmoothBaseCriterion

/-!
# The nonzero smooth locus in the affine universal coefficient space

The complement of the zero coefficient vector is an actual open. Intersecting
it with the maximal smooth base gives precisely the parameters whose residue
equation is nonzero and whose actual projective fiber is smooth. Its universal
family is proper and smooth, and its local rings are regular over a regular
coefficient base. Passing to projective coefficient space remains separate.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
attribute [local instance] PrimeSpectrum.isPrime
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)

/-- The coefficient of each prescribed monomial is its independent universal
coefficient variable. -/
theorem form_coeff (m : Monomials σ d) :
    (form σ d R).coeff m.1 = MvPolynomial.X m := by
  classical
  simp only [form, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _ him
    have hne : m.1 ≠ i.1 := fun h ↦ him (Subtype.ext h.symm)
    simp [Ne.symm hne]
  · simp

/-- The affine coefficient open consisting of nonzero equations. -/
noncomputable def nonzeroParameterOpen : (Spec (.of (Coefficients σ d R))).Opens :=
  ⨆ m : Monomials σ d, PrimeSpectrum.basicOpen (MvPolynomial.X m)

/-- Membership in the nonzero coefficient open is exactly nonzeroness of
the equation over the point's residue field. -/
theorem mem_nonzeroParameterOpen_iff (y : PrimeSpectrum (Coefficients σ d R)) :
    y ∈ nonzeroParameterOpen R σ d ↔
      (form σ d R).map (algebraMap (Coefficients σ d R) y.asIdeal.ResidueField) ≠ 0 := by
  classical
  change y ∈ (⨆ m : Monomials σ d, PrimeSpectrum.basicOpen (MvPolynomial.X m) :
    TopologicalSpace.Opens (PrimeSpectrum (Coefficients σ d R))) ↔ _
  rw [TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨m, hm⟩ hz
    have hc := congrArg (MvPolynomial.coeff m.1) hz
    rw [MvPolynomial.coeff_map, form_coeff, MvPolynomial.coeff_zero] at hc
    exact hm (Ideal.algebraMap_residueField_eq_zero.mp hc)
  · intro hn
    by_contra h
    apply hn
    simp only [form, map_sum, MvPolynomial.map_monomial]
    apply Finset.sum_eq_zero
    intro m _
    have hm : MvPolynomial.X m ∈ y.asIdeal := by
      by_contra hm
      exact h ⟨m, hm⟩
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hm, MvPolynomial.monomial_zero]

/-- The nonzero smooth parameter locus in the affine coefficient space. -/
noncomputable def nonzeroSmoothParameterOpen [IsNoetherianRing R] :
    (Spec (.of (Coefficients σ d R))).Opens :=
  nonzeroParameterOpen R σ d ⊓ smoothParameterOpen R σ d

/-- This open classifies exactly nonzero residue equations with smooth actual
projective fibers; the flatness needed for the converse is proved internally. -/
theorem mem_nonzeroSmoothParameterOpen_iff [IsNoetherianRing R]
    (y : PrimeSpectrum (Coefficients σ d R)) :
    y ∈ nonzeroSmoothParameterOpen R σ d ↔
      (form σ d R).map (algebraMap (Coefficients σ d R) y.asIdeal.ResidueField) ≠ 0 ∧
      Smooth ((familyToCoefficients R σ d).fiberToSpecResidueField y) := by
  change (y ∈ nonzeroParameterOpen R σ d ∧ y ∈ smoothParameterOpen R σ d) ↔ _
  rw [mem_nonzeroParameterOpen_iff]
  constructor
  · rintro ⟨hn, hs⟩
    exact ⟨hn, smooth_fiber_of_mem_properSmoothBase (familyToCoefficients R σ d) y hs⟩
  · rintro ⟨hn, hs⟩
    refine ⟨hn, ?_⟩
    exact (mem_properSmoothBase_hypersurface_iff_of_nonzero_residue
      (form σ d R) (form_isHomogeneous σ d R) y hn).mpr hs

/-- The universal family over the nonzero smooth locus is smooth. -/
theorem smooth_family_over_nonzeroSmoothParameterOpen [IsNoetherianRing R] :
    Smooth (familyToCoefficients R σ d ∣_ nonzeroSmoothParameterOpen R σ d) := by
  apply (smooth_morphismRestrict_iff_le_properSmoothBase (familyToCoefficients R σ d) _).mpr
  exact inf_le_right

/-- The universal family over the nonzero smooth locus remains proper. -/
theorem proper_family_over_nonzeroSmoothParameterOpen [IsNoetherianRing R] :
    IsProper (familyToCoefficients R σ d ∣_ nonzeroSmoothParameterOpen R σ d) :=
  IsZariskiLocalAtTarget.restrict (P := @IsProper.{u}) inferInstance _

/-- The local rings of the nonzero smooth parameter locus are regular over
any regular base ring, including the integers. -/
theorem isRegularLocalRing_nonzeroSmoothParameter_stalk [IsRegularRing R]
    (x : (nonzeroSmoothParameterOpen R σ d).toScheme) :
    IsRegularLocalRing ((nonzeroSmoothParameterOpen R σ d).toScheme.presheaf.stalk x) :=
  isRegularLocalRing_open_spec_stalk (Coefficients σ d R)
    (nonzeroSmoothParameterOpen R σ d) x

/-- The nonzero smooth parameter locus is smooth over the original coefficient
base ring. -/
theorem smooth_nonzeroSmoothParameterOpen_toBase [IsNoetherianRing R] :
    Smooth ((nonzeroSmoothParameterOpen R σ d).ι ≫ coefficientSchemeToBase R σ d) := by
  infer_instance

end UniversalHomogeneous
end AllCharacteristics
