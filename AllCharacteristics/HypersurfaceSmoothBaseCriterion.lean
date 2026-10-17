import AllCharacteristics.HypersurfaceCoefficientOpens
import AllCharacteristics.SmoothFiberOnFlatOpen

/-!
# Smooth-base membership for nonzero hypersurface equations

A coefficient which survives at a base point gives a proved flat neighborhood.
Consequently a nonzero residue equation has smooth fiber exactly when the base
point lies in the maximal open where the projective family is smooth. This
supplies the converse missing from the unrestricted affine coefficient family.
-/

open AlgebraicGeometry
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
attribute [local instance] PrimeSpectrum.isPrime

/-- If a coefficient survives at a base point, smoothness of the actual fiber
is equivalent to membership in the family's maximal smooth base open. -/
theorem mem_properSmoothBase_hypersurface_iff_of_coefficient_not_mem
    {R : Type u} {σ : Type} [CommRing R] [IsNoetherianRing R] [Finite σ]
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (y : PrimeSpectrum R) (m : σ →₀ ℕ) (hm : p.coeff m ∉ y.asIdeal) :
    y ∈ properSmoothBase (hypersurfaceToBase p hp) ↔
      Smooth ((hypersurfaceToBase p hp).fiberToSpecResidueField y) := by
  refine ⟨smooth_fiber_of_mem_properSmoothBase (hypersurfaceToBase p hp) y, ?_⟩
  intro hsm
  have := flat_hypersurface_on_coefficient_open p hp m
  apply mem_properSmoothBase_of_smooth_fiber_on_flat_open (hypersurfaceToBase p hp)
    (PrimeSpectrum.basicOpen (p.coeff m)) y _ hsm
  exact hm

/-- Every nonzero residue equation satisfies the smooth-fiber converse,
including in positive characteristic and over mixed-characteristic bases. -/
theorem mem_properSmoothBase_hypersurface_iff_of_nonzero_residue
    {R : Type u} {σ : Type} [CommRing R] [IsNoetherianRing R] [Finite σ]
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (y : PrimeSpectrum R)
    (hne : p.map (algebraMap R y.asIdeal.ResidueField) ≠ 0) :
    y ∈ properSmoothBase (hypersurfaceToBase p hp) ↔
      Smooth ((hypersurfaceToBase p hp).fiberToSpecResidueField y) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, (p.map (algebraMap R y.asIdeal.ResidueField)).coeff m ≠ 0 := by
    by_contra! h
    apply hne
    ext m
    simpa only [MvPolynomial.coeff_zero] using h m
  apply mem_properSmoothBase_hypersurface_iff_of_coefficient_not_mem p hp y m
  intro hmem
  apply hm
  rw [MvPolynomial.coeff_map]
  exact Ideal.algebraMap_residueField_eq_zero.mpr hmem

end HomogeneousProjective
end AllCharacteristics
