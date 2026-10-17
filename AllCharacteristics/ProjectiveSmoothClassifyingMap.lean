import AllCharacteristics.ProjectiveClassifyingMap
import AllCharacteristics.UniversalProjectiveSmoothEquation

/-!
# The coefficient-independent smooth classifying map

The projective classifying map factors through the smooth parameter open
exactly for smooth equations. Its factorization is independent of the chosen
coefficient, and the original hypersurface is the actual restricted universal
fiber over the original field.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
variable {σ : Type} [Finite σ] {d : ℕ}
variable (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hne : p ≠ 0) (b : R →+* k)

/-- The coefficient-independent parameter belongs to the smooth open exactly
when the original hypersurface is smooth. -/
theorem projectiveClassifyingMap_mem_smooth_iff :
    projectiveClassifyingMap p hp hne b (IsLocalRing.closedPoint k) ∈
      projectiveSmoothParameterOpen R σ d ↔ Smooth (hypersurfaceToBase p hp) :=
  projectiveEquationParameter_mem_smooth_iff b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne) hp

variable [Smooth (hypersurfaceToBase p hp)]

/-- The coefficient-independent classifying morphism of a nonzero smooth equation. -/
noncomputable def projectiveSmoothClassifyingMap :
    Spec (.of k) ⟶ (projectiveSmoothParameterOpen R σ d).toScheme :=
  projectiveSmoothEquationParameter b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne) hp

/-- The smooth factorization recovers the original projective classifying morphism. -/
theorem projectiveSmoothClassifyingMap_fac :
    projectiveSmoothClassifyingMap p hp hne b ≫ (projectiveSmoothParameterOpen R σ d).ι =
      projectiveClassifyingMap p hp hne b :=
  projectiveSmoothEquationParameter_fac b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne) hp

/-- Every normalized smooth chart construction gives exactly this factorization. -/
theorem projectiveSmoothClassifyingMap_eq_chart (j : Monomials σ d) (hj : p.coeff j.1 ≠ 0) :
    projectiveSmoothClassifyingMap p hp hne b = projectiveSmoothEquationParameter b p j hj hp := by
  apply (cancel_mono (projectiveSmoothParameterOpen R σ d).ι).mp
  rw [projectiveSmoothClassifyingMap_fac, projectiveSmoothEquationParameter_fac,
    projectiveClassifyingMap_eq_chart p hp hne b j hj]

/-- The smooth classifying morphism retains the original coefficient-ring map. -/
theorem projectiveSmoothClassifyingMap_toBase :
    projectiveSmoothClassifyingMap p hp hne b ≫
      (projectiveSmoothParameterOpen R σ d).ι ≫ projectiveParametersToBase R σ d =
        Spec.map (CommRingCat.ofHom b) := by
  rw [← Category.assoc, projectiveSmoothClassifyingMap_fac, projectiveClassifyingMap_toBase]

/-- The original smooth hypersurface is the actual restricted universal fiber
at its coefficient-independent parameter. -/
noncomputable def projectiveSmoothClassifyingFiberIso :
    hypersurface p hp ≅ pullback (projectiveSmoothFamilyToBase R σ d)
      (projectiveSmoothClassifyingMap p hp hne b) :=
  projectiveSmoothEquationFiberIso b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne) hp

/-- The restricted fiber identification is over the original field. -/
theorem projectiveSmoothClassifyingFiberIso_hom_snd :
    (projectiveSmoothClassifyingFiberIso p hp hne b).hom ≫
      pullback.snd (projectiveSmoothFamilyToBase R σ d) (projectiveSmoothClassifyingMap p hp hne b) =
        hypersurfaceToBase p hp :=
  projectiveSmoothEquationFiberIso_hom_snd b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne) hp

end UniversalHomogeneous
end AllCharacteristics
