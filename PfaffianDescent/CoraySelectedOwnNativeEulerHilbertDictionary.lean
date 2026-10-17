import PfaffianDescent.CorayOwnNativeEulerDefinitions
import PfaffianDescent.CorayOwnPositiveNativeEulerDegreeStepAnyField
import PfaffianDescent.CorayOwnPositiveNativeHilbertDictionary
import PfaffianDescent.CorayOwnLiteralPositiveIntrinsicHOne

/-! SAME original component eventual native Euler/Hilbert dictionary, constructed inputs. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine OWN coordinate cokernel rank gives the full affine Euler
formula in every twist. This keeps the original unit Euler constant. -/
theorem selectedProjectiveMinimalComponent_ownPositiveNativeEuler_affine
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal PS)
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) (j : Fin 4) (hj : coordinate C j ∉ P.asHomogeneousIdeal)
    [HasExt.{u} (scheme C).Modules] (m : ℕ) :
    ownPositiveNativeEuler C m = ownUnitNativeEuler C +
      (m : ℤ) * actualCurveCoordinateHilbertDegree C := by
  induction m with
  | zero => simpa using ownPositiveNativeEuler_zero_eq_unit C
  | succ m ih =>
    have hs : ownPositiveNativeEuler C (m + 1) = ownPositiveNativeEuler C m +
        actualCurveCoordinateHilbertDegree C :=
      selectedProjectiveMinimalComponent_ownPositiveCoordinate_nativeEuler_step_degree_anyField
        p q hp hp0 n hq hnot C hCmin P j hj m
    rw [hs, ih]
    push_cast
    ring

/-- Genuine intrinsic positive H1 vanishing. Ambient HasExt is constructed,
and the original quotient coefficient Iso supplies the actual transport. -/
theorem homogeneousIdeal_eventually_ownPositive_cohomology_one_subsingleton
    (C : HomogeneousIdeal PS) [HasExt.{u} (scheme C).Modules] :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Subsingleton (schemeModuleCohomology (scheme C)
        (positiveSheafOfModules (grading C) m) 1) := by
  exact homogeneousIdeal_eventually_actualOwnPositive_cohomology_one_subsingleton001 C

/-- Actual OWN coordinate Hilbert function eventually equals native Euler.
Both comparisons and H1 vanishing are internally derived; the original
constants rank remains in ownUnitNativeEuler. -/
theorem selectedProjectiveMinimalComponent_eventually_ownGrade_nativeEuler_affine
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal PS)
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) (j : Fin 4) (hj : coordinate C j ∉ P.asHomogeneousIdeal)
    [HasExt.{u} (scheme C).Modules] :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      (Module.finrank K (grading C m) : ℤ) = ownUnitNativeEuler C +
        (m : ℤ) * actualCurveCoordinateHilbertDegree C := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  obtain ⟨B0, hB0⟩ :=
    selectedProjectiveMinimalComponent_eventually_ownPositiveTwist_topSections_finite_and_gradeRank
      p q hp hp0 n hq hnot C hCmin P
  obtain ⟨B1, hB1⟩ := homogeneousIdeal_eventually_ownPositive_cohomology_one_subsingleton C
  refine ⟨max B0 B1, fun m hm => ?_⟩
  letI := hB1 m ((Nat.le_max_right B0 B1).trans hm)
  have hH1 : Module.finrank K (schemeModuleCohomology (scheme C)
      (positiveSheafOfModules (grading C) m) 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hH0 := (hB0 m ((Nat.le_max_left B0 B1).trans hm)).2
  have hE := selectedProjectiveMinimalComponent_ownPositiveNativeEuler_affine
    p q hp hp0 n hq hnot C hCmin P j hj m
  change ((Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
      (positiveSheafOfModules (grading C) m) ⊤) : ℤ) -
      Module.finrank K (schemeModuleCohomology (scheme C)
        (positiveSheafOfModules (grading C) m) 1)) = _ at hE
  rw [hH0, hH1] at hE
  simpa only [Nat.cast_zero, sub_zero] using hE

end PfaffianDescent.Coray
