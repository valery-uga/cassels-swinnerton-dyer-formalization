import AllCharacteristics.UniversalHomogeneous
import AllCharacteristics.ProperSmoothBase
import AllCharacteristics.RegularAffineStalks
import AllCharacteristics.HypersurfaceReduction

/-!
# A regular affine parameter open with a smooth universal family

The universal homogeneous family is restricted to its maximal smooth base
open. Over a regular coefficient ring, this open has regular local stalks;
it is also smooth over the coefficient ring. Its fibers are identified with
the hypersurfaces of the specialized equations. The nonzero residue-equation
converse and the resulting locus are proved in `UniversalNonzeroSmoothLocus`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)

/-- The proper universal family is locally of finite presentation over a
noetherian coefficient base. -/
instance locallyOfFinitePresentation_familyToCoefficients [IsNoetherianRing R] :
    LocallyOfFinitePresentation (familyToCoefficients R σ d) := by infer_instance

/-- The maximal affine coefficient open over which the whole universal
homogeneous family is smooth. -/
noncomputable def smoothParameterOpen [IsNoetherianRing R] :
    (Spec (.of (Coefficients σ d R))).Opens :=
  properSmoothBase (familyToCoefficients R σ d)

/-- The actual universal family restricted to the smooth coefficient open. -/
noncomputable def smoothParameterFamily [IsNoetherianRing R] : Scheme.{u} :=
  ((familyToCoefficients R σ d) ⁻¹ᵁ smoothParameterOpen R σ d).toScheme

/-- The restricted universal family maps to its smooth parameter base. -/
noncomputable def smoothParameterFamilyToBase [IsNoetherianRing R] :
    smoothParameterFamily R σ d ⟶ (smoothParameterOpen R σ d).toScheme :=
  familyToCoefficients R σ d ∣_ smoothParameterOpen R σ d

/-- The restricted universal family is proper over its parameter base. -/
instance isProper_smoothParameterFamilyToBase [IsNoetherianRing R] :
    IsProper (smoothParameterFamilyToBase R σ d) := by
  exact IsZariskiLocalAtTarget.restrict (P := @IsProper.{u})
    (inferInstance : IsProper (familyToCoefficients R σ d)) (smoothParameterOpen R σ d)

/-- The restricted universal family is smooth over its parameter base. -/
instance smooth_smoothParameterFamilyToBase [IsNoetherianRing R] :
    Smooth (smoothParameterFamilyToBase R σ d) :=
  smooth_on_properSmoothBase (familyToCoefficients R σ d)

/-- The smooth affine parameter open is noetherian over a noetherian base. -/
theorem isNoetherian_smoothParameterOpen [IsNoetherianRing R] :
    IsNoetherian (smoothParameterOpen R σ d).toScheme := by
  have : TopologicalSpace.NoetherianSpace (smoothParameterOpen R σ d).toScheme :=
    TopologicalSpace.NoetherianSpace.set
      (smoothParameterOpen R σ d : Set (Spec (.of (Coefficients σ d R))))
  exact {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := TopologicalSpace.NoetherianSpace.compactSpace _ }

/-- The local rings of the smooth affine parameter open are regular whenever
the coefficient base is regular, in particular over the integers or a field. -/
theorem isRegularLocalRing_smoothParameter_stalk [IsRegularRing R]
    (x : (smoothParameterOpen R σ d).toScheme) :
    IsRegularLocalRing ((smoothParameterOpen R σ d).toScheme.presheaf.stalk x) :=
  isRegularLocalRing_open_spec_stalk (Coefficients σ d R) (smoothParameterOpen R σ d) x

/-- The affine coefficient scheme has its natural map to the coefficient base. -/
noncomputable def coefficientSchemeToBase :
    Spec (.of (Coefficients σ d R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Coefficients σ d R)))

/-- The affine coefficient scheme is smooth over its coefficient base. -/
instance smooth_coefficientSchemeToBase : Smooth (coefficientSchemeToBase R σ d) := by
  unfold coefficientSchemeToBase
  apply (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr
  apply RingHom.smooth_algebraMap.mpr
  exact { formallySmooth := inferInstance, finitePresentation := inferInstance }

/-- The smooth parameter open is itself smooth over the original coefficient
base, including the mixed-characteristic integer base. -/
theorem smooth_parameterOpen_toBase [IsNoetherianRing R] :
    Smooth ((smoothParameterOpen R σ d).ι ≫ coefficientSchemeToBase R σ d) := by
  infer_instance

/-- A coefficient specialization landing in the constructed parameter open
defines a smooth actual projective hypersurface over its target field. -/
theorem smooth_hypersurface_of_parameter_mem [IsNoetherianRing R]
    {k : Type u} [Field k] (b : R →+* k) (p : MvPolynomial σ k)
    (hp : p.IsHomogeneous d)
    (hmem : (Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom b (fun m : Monomials σ d ↦ p.coeff m.1))))
        (IsLocalRing.closedPoint k) ∈ smoothParameterOpen R σ d) :
    Smooth (hypersurfaceToBase p hp) := by
  let c := MvPolynomial.eval₂Hom b (fun m : Monomials σ d ↦ p.coeff m.1)
  have hr : Set.range (Spec.map (CommRingCat.ofHom c)) ⊆ smoothParameterOpen R σ d := by
    rintro _ ⟨y, rfl⟩
    have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    change (Spec.map (CommRingCat.ofHom c)) y ∈ smoothParameterOpen R σ d
    rw [hy]
    exact hmem
  have hs : Smooth (pullback.snd (familyToCoefficients R σ d)
      (Spec.map (CommRingCat.ofHom c))) :=
    smooth_pullback_of_range_subset_properSmoothBase (familyToCoefficients R σ d) _ hr
  have he : (form σ d R).map c = p := map_form_eq b p hp
  have hid := hypersurfaceReductionIso_hom_snd c (form σ d R) (form_isHomogeneous σ d R) p hp he
  rw [← hid]
  exact @smooth_comp _ _ _ _ _ inferInstance hs

end UniversalHomogeneous
end AllCharacteristics
