import AllCharacteristics.UniversalProjectiveSmoothLocus
import AllCharacteristics.UniversalProjectiveEquationFiber
import AllCharacteristics.ProperSmoothBaseOpenChange
import AllCharacteristics.SmoothFiberReflection

/-!
# Smooth equations in the projective universal parameter open

For every field and every chosen nonzero coefficient, a homogeneous equation's
projective parameter lies in the smooth open exactly when its hypersurface is
smooth. The proof retains inseparable extensions. The smooth equation itself
is the actual fiber of the restricted proper smooth universal family.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
variable {σ : Type} [Finite σ] {d : ℕ}
variable (b : R →+* k) (p : MvPolynomial σ k)
variable (j : Monomials σ d) (hj : p.coeff j.1 ≠ 0) (hp : p.IsHomogeneous d)

/-- A smooth homogeneous equation defines a point of the projective smooth
parameter open over an arbitrary field. -/
theorem projectiveEquationParameter_mem_smooth_of_smooth
    [Smooth (hypersurfaceToBase p hp)] :
    projectiveEquationParameter b p j hj (IsLocalRing.closedPoint k) ∈
      projectiveSmoothParameterOpen R σ d := by
  let c := Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj))
  have he := (projectiveEquationChartFiberIso b p j hj hp).inv_comp_eq.mpr
    (projectiveEquationChartFiberIso_hom_snd b p j hj hp).symm
  have hs : Smooth (pullback.snd (normalizedFamilyToBase R σ d j) c) := by
    rw [← he]
    exact @smooth_comp _ _ _ _ _ inferInstance inferInstance
  have hf := smooth_fiber_of_smooth_pullback (normalizedFamilyToBase R σ d j) c
    (IsLocalRing.closedPoint k)
  have hm := (mem_properSmoothBase_iff_smooth_fiber (normalizedFamilyToBase R σ d j)
    (c (IsLocalRing.closedPoint k))).mpr hf
  exact (mem_properSmoothBase_iff_of_open_baseChange
    (isPullback_projectiveUniversalChart R σ d j) (c (IsLocalRing.closedPoint k))).mp hm

/-- For a nonzero coefficient, membership in the projective smooth open is
exactly smoothness of the original equation's hypersurface. -/
theorem projectiveEquationParameter_mem_smooth_iff :
    projectiveEquationParameter b p j hj (IsLocalRing.closedPoint k) ∈
      projectiveSmoothParameterOpen R σ d ↔ Smooth (hypersurfaceToBase p hp) := by
  constructor
  · intro hm
    have hr : Set.range (projectiveEquationParameter b p j hj) ⊆
        projectiveSmoothParameterOpen R σ d := by
      rintro _ ⟨y, rfl⟩
      have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      rw [hy]
      exact hm
    have hs := smooth_pullback_of_range_subset_properSmoothBase (projectiveUniversalToBase R σ d)
      (projectiveEquationParameter b p j hj) hr
    rw [← projectiveEquationFiberIso_hom_snd b p j hj hp]
    exact @smooth_comp _ _ _ _ _ inferInstance hs
  · intro hs
    exact projectiveEquationParameter_mem_smooth_of_smooth b p j hj hp

variable [Smooth (hypersurfaceToBase p hp)]
include hp

/-- The whole field spectrum of a smooth equation maps into the projective smooth open. -/
theorem projectiveEquationParameter_range_smooth :
    Set.range (projectiveEquationParameter b p j hj) ⊆ projectiveSmoothParameterOpen R σ d := by
  rintro _ ⟨y, rfl⟩
  have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  rw [hy]
  exact projectiveEquationParameter_mem_smooth_of_smooth b p j hj hp

/-- The actual classifying parameter in the projective smooth open. -/
noncomputable def projectiveSmoothEquationParameter :
    Spec (.of k) ⟶ (projectiveSmoothParameterOpen R σ d).toScheme :=
  IsOpenImmersion.lift (projectiveSmoothParameterOpen R σ d).ι
    (projectiveEquationParameter b p j hj) (by
      rw [(projectiveSmoothParameterOpen R σ d).range_ι]
      exact projectiveEquationParameter_range_smooth b p j hj hp)

/-- The classifying parameter lifts the original projective equation parameter. -/
theorem projectiveSmoothEquationParameter_fac :
    projectiveSmoothEquationParameter b p j hj hp ≫ (projectiveSmoothParameterOpen R σ d).ι =
      projectiveEquationParameter b p j hj :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted-family fiber is also a fiber of the global projective family. -/
theorem isPullback_projectiveSmoothFamily_equationParameter :
    IsPullback
      (pullback.fst (projectiveSmoothFamilyToBase R σ d) (projectiveSmoothEquationParameter b p j hj hp) ≫
        ((projectiveUniversalToBase R σ d) ⁻¹ᵁ projectiveSmoothParameterOpen R σ d).ι)
      (pullback.snd (projectiveSmoothFamilyToBase R σ d) (projectiveSmoothEquationParameter b p j hj hp))
      (projectiveUniversalToBase R σ d) (projectiveEquationParameter b p j hj) := by
  have h := (IsPullback.of_hasPullback (projectiveSmoothFamilyToBase R σ d)
    (projectiveSmoothEquationParameter b p j hj hp)).paste_horiz
      (isPullback_morphismRestrict (projectiveUniversalToBase R σ d)
        (projectiveSmoothParameterOpen R σ d)).flip
  simpa only [projectiveSmoothEquationParameter_fac] using h

/-- The given smooth hypersurface is the actual fiber of the restricted proper
smooth projective universal family. -/
noncomputable def projectiveSmoothEquationFiberIso :
    hypersurface p hp ≅ pullback (projectiveSmoothFamilyToBase R σ d)
      (projectiveSmoothEquationParameter b p j hj hp) :=
  projectiveEquationFiberIso b p j hj hp ≪≫
    (isPullback_projectiveSmoothFamily_equationParameter b p j hj hp).isoPullback.symm

/-- This restricted fiber identification preserves the equation's original field. -/
theorem projectiveSmoothEquationFiberIso_hom_snd :
    (projectiveSmoothEquationFiberIso b p j hj hp).hom ≫
      pullback.snd (projectiveSmoothFamilyToBase R σ d) (projectiveSmoothEquationParameter b p j hj hp) =
        hypersurfaceToBase p hp := by
  change ((projectiveEquationFiberIso b p j hj hp).hom ≫
    (isPullback_projectiveSmoothFamily_equationParameter b p j hj hp).isoPullback.inv) ≫ _ = _
  rw [Category.assoc, IsPullback.isoPullback_inv_snd]
  exact projectiveEquationFiberIso_hom_snd b p j hj hp

end UniversalHomogeneous
end AllCharacteristics
