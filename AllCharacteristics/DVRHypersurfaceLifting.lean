import AllCharacteristics.DVRProjectiveFlatness
import AllCharacteristics.ProjectiveFiberSmoothness
import AllCharacteristics.ResidueFiberSmoothness
import AllCharacteristics.UniversalHomogeneous
import AllCharacteristics.SurjectiveResiduePresentation

/-!
# Smooth lifting of homogeneous hypersurfaces over a given DVR

A homogeneous equation with nonzero smooth reduction defines a smooth proper
family over the DVR. Every nonzero smooth homogeneous equation over a residue
field admits such a lift. The residue field may be given by any surjective
homomorphism, and no perfection or characteristic hypothesis is imposed.
This module does not construct the DVR itself.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Finite σ]

/-- A homogeneous equation over a DVR whose reduction is nonzero and smooth
defines a smooth family over the entire DVR. -/
theorem smooth_hypersurfaceToBase_of_smooth_reduction
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (hred : p.map (residue R) ≠ 0)
    [Smooth (hypersurfaceToBase (p.map (residue R)) (hp.map (residue R)))] :
    Smooth (hypersurfaceToBase p hp) := by
  have := flat_hypersurfaceToBase_of_nonzero_reduction p hp hred
  have := smooth_hypersurface_pullback_of_smooth_map (residue R) p hp
  exact smooth_of_smooth_residue_pullback R (hypersurfaceToBase p hp)

/-- Over a given DVR, every nonzero smooth homogeneous residue equation has
a homogeneous lift defining a smooth proper projective family. -/
theorem exists_smooth_homogeneous_lift
    (p : MvPolynomial σ (ResidueField R)) {d : ℕ} (hp : p.IsHomogeneous d)
    (hne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    ∃ q : MvPolynomial σ R, ∃ hq : q.IsHomogeneous d,
      q.map (residue R) = p ∧ Smooth (hypersurfaceToBase q hq) := by
  obtain ⟨q, hq, he⟩ := UniversalHomogeneous.exists_homogeneous_lift
    (residue R) residue_surjective p hp
  have hred : q.map (residue R) ≠ 0 := he ▸ hne
  have hs : Smooth (hypersurfaceToBase (q.map (residue R)) (hq.map (residue R))) := by
    cases he
    infer_instance
  exact ⟨q, hq, he, smooth_hypersurfaceToBase_of_smooth_reduction q hq hred⟩

/-- A smooth homogeneous hypersurface over any presented residue field lifts
to a smooth proper family over the given DVR, with the exact prescribed
coefficient reduction. Inseparable and imperfect residue fields are allowed. -/
theorem exists_smooth_homogeneous_lift_of_surjective
    {k : Type u} [Field k] (b : R →+* k) (hb : Function.Surjective b)
    (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d)
    (hne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    ∃ q : MvPolynomial σ R, ∃ hq : q.IsHomogeneous d,
      q.map b = p ∧ Smooth (hypersurfaceToBase q hq) := by
  obtain ⟨q, hq, he⟩ := UniversalHomogeneous.exists_homogeneous_lift b hb p hp
  let e := residueEquivOfSurjective b hb
  have hc : e.symm.toRingHom.comp b = residue R := by
    apply RingHom.ext
    intro r
    apply e.injective
    exact (e.apply_symm_apply (b r)).trans
      (residueEquivOfSurjective_residue b hb r).symm
  have hmap : q.map (residue R) = p.map e.symm.toRingHom := by
    rw [← he, MvPolynomial.map_map, hc]
  have hred : q.map (residue R) ≠ 0 := by
    rw [hmap]
    intro hz
    apply hne
    exact MvPolynomial.map_injective e.symm.toRingHom e.symm.injective
      (hz.trans (map_zero (MvPolynomial.map e.symm.toRingHom)).symm)
  have hs' := smooth_hypersurfaceToBase_map e.symm.toRingHom p hp
  have hs : Smooth (hypersurfaceToBase (q.map (residue R)) (hq.map (residue R))) := by
    exact (smooth_hypersurfaceToBase_congr _ _ _ _ hmap).mpr hs'
  exact ⟨q, hq, he, smooth_hypersurfaceToBase_of_smooth_reduction q hq hred⟩

end HomogeneousProjective
end AllCharacteristics
