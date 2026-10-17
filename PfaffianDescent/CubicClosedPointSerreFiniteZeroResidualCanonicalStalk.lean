import PfaffianDescent.CubicClosedPointSerreLocalKoszulNativeAlignment

/-! # The actual canonical Serre section cuts out the original maximal ideal

The native point ideal coordinate, regular generators, and stalk freeness
are constructed by the original Serre extension.  Thus the canonical section's
coordinate ideal is the maximal ideal, without a supplied local presentation.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_span_coordinates_map_le
    {R : Type u} [CommRing R] (a : (R × R) →ₗ[R] R × R) (z : R × R) :
    Ideal.span ({(a z).1, (a z).2} : Set R) ≤ Ideal.span ({z.1, z.2} : Set R) := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
  have hc (k : R × R →ₗ[R] R) : k z ∈ Ideal.span ({z.1, z.2} : Set R) := by
    rw [hz, map_add, map_smul, map_smul]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  apply Ideal.span_le.mpr
  rintro r (hr | hr)
  · rw [hr]
    exact hc ((LinearMap.fst R R R).comp a)
  · rw [hr]
    exact hc ((LinearMap.snd R R R).comp a)

theorem cubicClosedPointSerreFiniteZeroResidual_span_coordinates_equiv
    {R : Type u} [CommRing R] (a : (R × R) ≃ₗ[R] R × R) (z : R × R) :
    Ideal.span ({(a z).1, (a z).2} : Set R) = Ideal.span ({z.1, z.2} : Set R) := by
  apply le_antisymm
  · exact cubicClosedPointSerreFiniteZeroResidual_span_coordinates_map_le a.toLinearMap z
  · have h := cubicClosedPointSerreFiniteZeroResidual_span_coordinates_map_le a.symm.toLinearMap (a z)
    change Ideal.span ({(a.symm (a z)).1, (a.symm (a z)).2} : Set R) ≤ _ at h
    simpa only [LinearEquiv.symm_apply_apply] using h

namespace ProjectiveNegativeTwist
open AllCharacteristics.HomogeneousProjective
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_stalk_span
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e hExt)
        (show 1 + 1 = 2 by omega) ≠ 0) :
    let X := hypersurface p hp
    let x := i default
    let N : X.Modules := e.E
    letI : Module (X.presheaf.stalk x) (N.presheaf.stalk x) := schemeModuleStalkModule N x
    ∀ t : (N.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
        (X.presheaf.stalk x) × (X.presheaf.stalk x),
      Ideal.span ({(t (serreExtensionStalkCanonicalSection e x 1)).1,
        (t (serreExtensionStalkCanonicalSection e x 1)).2} : Set (X.presheaf.stalk x)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  dsimp only
  let X := hypersurface p hp
  let x := i default
  let R := X.presheaf.stalk x
  let N : X.Modules := e.E
  let M : X.Modules := closedImmersionIdealTwist i
    (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
  letI : Module R (N.presheaf.stalk x) := schemeModuleStalkModule N x
  letI : Module R (M.presheaf.stalk x) := schemeModuleStalkModule M x
  let d := Classical.choice (cubicClosedPointSerreLocalKoszulNative_exists_chart K p hp hp0 i)
  let xU : d.U := ⟨x, d.mem⟩
  obtain ⟨a, _, _⟩ := cubicClosedPointSerreLocalKoszulFree_exists_idealCoordinate
    i (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
    d.U d.q d.f d.twist d.sequence xU
  let q := X.presheaf.germ d.U x d.mem d.q
  let f := X.presheaf.germ d.U x d.mem d.f
  have hspan : Ideal.span ({q, f} : Set R) = IsLocalRing.maximalIdeal R := d.span_maximal
  have hq : q ∈ IsLocalRing.maximalIdeal R :=
    hspan ▸ Ideal.subset_span (by simp)
  have hf : f ∈ IsLocalRing.maximalIdeal R :=
    hspan ▸ Ideal.subset_span (by simp)
  have hfree : Module.Free R (N.presheaf.stalk x) :=
    cubicClosedPointSerreLocalFree_stalk_free K p hp hp0 i e hne
  obtain ⟨t₀, ht₀⟩ := serreExtension_stalk_exists_freeCoordinates_of_quotientEquiv_at_lci_point
    e x q f a.toLinearEquiv d.regular_first d.regular_second hq hf hfree
  intro t
  have heq := cubicClosedPointSerreFiniteZeroResidual_span_coordinates_equiv
    (t₀.symm.trans t) (t₀ (serreExtensionStalkCanonicalSection e x 1))
  simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
    heq.trans (ht₀.trans hspan)

end ProjectiveNegativeTwist
end PfaffianDescent
