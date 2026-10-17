import AllCharacteristics.UniversalFieldParameters

/-!
# Every nonzero smooth equation is a fiber of the restricted universal family

The equation's coefficient morphism factors through the nonzero smooth locus.
The actual projective hypersurface is isomorphic, over its coefficient field,
to the pullback of the restricted universal family along this factorization.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (σ : Type) [Finite σ] (d : ℕ)

/-- The universal homogeneous family restricted to the nonzero smooth locus. -/
noncomputable def nonzeroSmoothFamily : Scheme.{u} :=
  ((familyToCoefficients R σ d) ⁻¹ᵁ nonzeroSmoothParameterOpen R σ d).toScheme

/-- The restricted universal family over its actual parameter scheme. -/
noncomputable def nonzeroSmoothFamilyToBase :
    nonzeroSmoothFamily R σ d ⟶ (nonzeroSmoothParameterOpen R σ d).toScheme :=
  familyToCoefficients R σ d ∣_ nonzeroSmoothParameterOpen R σ d

/-- The named universal family over the nonzero smooth locus is proper. -/
instance isProper_nonzeroSmoothFamilyToBase : IsProper (nonzeroSmoothFamilyToBase R σ d) :=
  proper_family_over_nonzeroSmoothParameterOpen R σ d

/-- The named universal family over the nonzero smooth locus is smooth. -/
instance smooth_nonzeroSmoothFamilyToBase : Smooth (nonzeroSmoothFamilyToBase R σ d) :=
  smooth_family_over_nonzeroSmoothParameterOpen R σ d

variable {R σ d} {k : Type u} [Field k]
variable (b : R →+* k) (p : MvPolynomial σ k) (hp : p.IsHomogeneous d)
variable (hne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]

include hp hne in
/-- The whole field spectrum maps into the nonzero smooth parameter locus. -/
theorem equationParameter_range_nonzeroSmooth :
    Set.range (equationParameter (d := d) b p) ⊆ nonzeroSmoothParameterOpen R σ d := by
  rintro _ ⟨y, rfl⟩
  have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  change equationParameter (d := d) b p y ∈ nonzeroSmoothParameterOpen R σ d
  rw [hy]
  exact equationParameter_mem_nonzeroSmooth_of_smooth b p hp hne

/-- The classifying field-valued point in the actual nonzero smooth locus. -/
noncomputable def smoothEquationParameter :
    Spec (.of k) ⟶ (nonzeroSmoothParameterOpen R σ d).toScheme :=
  IsOpenImmersion.lift (nonzeroSmoothParameterOpen R σ d).ι
    (equationParameter (d := d) b p) (by
      rw [(nonzeroSmoothParameterOpen R σ d).range_ι]
      exact equationParameter_range_nonzeroSmooth b p hp hne)

/-- Forgetting the open-locus factorization recovers the original coefficient
morphism exactly. -/
theorem smoothEquationParameter_fac :
    smoothEquationParameter b p hp hne ≫ (nonzeroSmoothParameterOpen R σ d).ι =
      equationParameter (d := d) b p :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted-family pullback is also the pullback of the original
universal family by the equation's coefficient morphism. -/
theorem isPullback_restrictedFamily_equationParameter :
    IsPullback
      (pullback.fst (nonzeroSmoothFamilyToBase R σ d) (smoothEquationParameter b p hp hne) ≫
        ((familyToCoefficients R σ d) ⁻¹ᵁ nonzeroSmoothParameterOpen R σ d).ι)
      (pullback.snd (nonzeroSmoothFamilyToBase R σ d) (smoothEquationParameter b p hp hne))
      (familyToCoefficients R σ d) (equationParameter (d := d) b p) := by
  have h := (IsPullback.of_hasPullback (nonzeroSmoothFamilyToBase R σ d)
    (smoothEquationParameter b p hp hne)).paste_horiz
      (isPullback_morphismRestrict (familyToCoefficients R σ d)
        (nonzeroSmoothParameterOpen R σ d)).flip
  simpa only [smoothEquationParameter_fac] using h

/-- The given projective hypersurface is the actual fiber of the restricted
universal family at its classifying parameter. -/
noncomputable def smoothEquationFiberIso :
    hypersurface p hp ≅
      pullback (nonzeroSmoothFamilyToBase R σ d) (smoothEquationParameter b p hp hne) :=
  hypersurfaceReductionIso (coefficientSpecialization (d := d) b p)
    (form σ d R) (form_isHomogeneous σ d R) p hp
    (map_form_coefficientSpecialization b p hp) ≪≫
      (isPullback_restrictedFamily_equationParameter b p hp hne).isoPullback.symm

/-- The fiber identification respects the original field structure map. -/
theorem smoothEquationFiberIso_hom_snd :
    (smoothEquationFiberIso b p hp hne).hom ≫
      pullback.snd (nonzeroSmoothFamilyToBase R σ d) (smoothEquationParameter b p hp hne) =
        hypersurfaceToBase p hp := by
  let e := hypersurfaceReductionIso (coefficientSpecialization (d := d) b p)
    (form σ d R) (form_isHomogeneous σ d R) p hp
    (map_form_coefficientSpecialization b p hp)
  let h := isPullback_restrictedFamily_equationParameter b p hp hne
  exact (Category.assoc e.hom h.isoPullback.inv
    (pullback.snd (nonzeroSmoothFamilyToBase R σ d) (smoothEquationParameter b p hp hne))).trans
      ((congrArg (fun t ↦ e.hom ≫ t) h.isoPullback_inv_snd).trans
        (hypersurfaceReductionIso_hom_snd _ _ _ _ _ _))

end UniversalHomogeneous
end AllCharacteristics
