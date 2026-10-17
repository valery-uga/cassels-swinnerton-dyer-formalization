import AllCharacteristics.UniversalNonzeroSmoothLocus
import AllCharacteristics.SmoothFiberReflection
import AllCharacteristics.FieldParameterResidue
import AllCharacteristics.ProjectiveFiberSmoothness

/-!
# Field-valued equations and the universal smooth parameter locus

Every homogeneous equation defines an actual coefficient specialization.
Its field-valued parameter lies in the nonzero smooth locus exactly when the
equation is nonzero and its projective hypersurface is smooth. The converse
uses residue-field descent, so inseparable field extensions are included.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
attribute [local instance] PrimeSpectrum.isPrime
variable {R k : Type u} [CommRing R] [Field k] {σ : Type} [Finite σ] {d : ℕ}

/-- Specialize the universal coefficient variables to an equation's coefficients. -/
noncomputable def coefficientSpecialization (b : R →+* k) (p : MvPolynomial σ k) :
    Coefficients σ d R →+* k :=
  MvPolynomial.eval₂Hom b (fun m : Monomials σ d ↦ p.coeff m.1)

/-- The actual field-valued point of the affine universal coefficient scheme. -/
noncomputable def equationParameter (b : R →+* k) (p : MvPolynomial σ k) :
    Spec (.of k) ⟶ Spec (.of (Coefficients σ d R)) :=
  Spec.map (CommRingCat.ofHom (coefficientSpecialization (d := d) b p))

/-- The universal equation specializes exactly to the given homogeneous equation. -/
theorem map_form_coefficientSpecialization
    (b : R →+* k) (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) :
    (form σ d R).map (coefficientSpecialization (d := d) b p) = p :=
  map_form_eq b p hp

/-- A field-valued parameter belongs to the nonzero open exactly when its
equation is nonzero. -/
theorem equationParameter_mem_nonzero_iff
    (b : R →+* k) (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) :
    equationParameter (d := d) b p (IsLocalRing.closedPoint k) ∈
      nonzeroParameterOpen R σ d ↔ p ≠ 0 := by
  let c := coefficientSpecialization (d := d) b p
  let y := PrimeSpectrum.comap c (IsLocalRing.closedPoint k)
  have hy : y.asIdeal = RingHom.ker c := fieldPoint_asIdeal_eq_ker c
  have hn := (mem_nonzeroParameterOpen_iff R σ d y).trans
    (mvPolynomial_residue_map_ne_zero_iff_field_map c y hy (form σ d R))
  rw [map_form_coefficientSpecialization b p hp] at hn
  exact hn

/-- A nonzero smooth homogeneous equation defines a point of the constructed
nonzero smooth parameter locus over any field. -/
theorem equationParameter_mem_nonzeroSmooth_of_smooth [IsNoetherianRing R]
    (b : R →+* k) (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    equationParameter (d := d) b p (IsLocalRing.closedPoint k) ∈
      nonzeroSmoothParameterOpen R σ d := by
  let c := coefficientSpecialization (d := d) b p
  have he : (form σ d R).map c = p := map_form_coefficientSpecialization b p hp
  have : Smooth (hypersurfaceToBase ((form σ d R).map c) ((form_isHomogeneous σ d R).map c)) :=
    (smooth_hypersurfaceToBase_congr _ p _ hp he).mpr inferInstance
  have hs : Smooth (pullback.snd (familyToCoefficients R σ d) (equationParameter (d := d) b p)) :=
    smooth_hypersurface_pullback_of_smooth_map c (form σ d R) (form_isHomogeneous σ d R)
  have hf := smooth_fiber_of_smooth_pullback (familyToCoefficients R σ d)
    (equationParameter (d := d) b p) (IsLocalRing.closedPoint k)
  have hn := (equationParameter_mem_nonzero_iff b p hp).mpr hne
  have hr := (mem_nonzeroParameterOpen_iff R σ d
    (PrimeSpectrum.comap c (IsLocalRing.closedPoint k))).mp hn
  exact (mem_nonzeroSmoothParameterOpen_iff R σ d _).mpr ⟨hr, hf⟩

/-- The actual field-valued points of the nonzero smooth locus classify
exactly the nonzero smooth homogeneous equations, in every characteristic. -/
theorem equationParameter_mem_nonzeroSmooth_iff [IsNoetherianRing R]
    (b : R →+* k) (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) :
    equationParameter (d := d) b p (IsLocalRing.closedPoint k) ∈
      nonzeroSmoothParameterOpen R σ d ↔ p ≠ 0 ∧ Smooth (hypersurfaceToBase p hp) := by
  constructor
  · intro h
    have hn : equationParameter (d := d) b p (IsLocalRing.closedPoint k) ∈
        nonzeroParameterOpen R σ d := h.1
    have hs : equationParameter (d := d) b p (IsLocalRing.closedPoint k) ∈
        smoothParameterOpen R σ d := h.2
    exact ⟨(equationParameter_mem_nonzero_iff b p hp).mp hn,
      smooth_hypersurface_of_parameter_mem R σ d b p hp hs⟩
  · rintro ⟨hn, hs⟩
    exact equationParameter_mem_nonzeroSmooth_of_smooth b p hp hn

end UniversalHomogeneous
end AllCharacteristics
