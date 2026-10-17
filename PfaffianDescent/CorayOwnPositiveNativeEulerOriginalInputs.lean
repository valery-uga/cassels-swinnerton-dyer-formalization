import PfaffianDescent.CorayOwnPositiveCoordinateNativeEulerStep
import PfaffianDescent.CorayOwnComponentProperConstants
import PfaffianDescent.CorayOwnPositivePullbackCohomologyVanishing
import PfaffianDescent.CorayOwnPositiveH1CoordinateDescent

/-! SOURCE ONLY. Original p/q and SAME component/point/coordinate derive
finite native H0/H1 of every positive twist, including actual constants at
zero. No PerfectField, geometrically-integral or finite-cohomology premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Properness derives the actual unit H0 finiteness, existing genuine
positive vanishing/descent derives unit H1 finiteness, and the actual acyclic
coordinate cokernel propagates BOTH to all positive twists. Constants are
never replaced by the ground field. -/
theorem selectedProjectivePrimeComponent_ownPositiveTwist_hZero_hOne_finite_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) [HasExt.{u} (scheme C).Modules] :
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    ∀ m : ℕ, Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
        (positiveSheafOfModules (grading C) m) ⊤) ∧
      Module.Finite K (schemeModuleCohomology (scheme C)
        (positiveSheafOfModules (grading C) m) 1) := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  letI : IsProper (toBase C) := isProper_toBase C
  let O : (scheme C).Modules := SheafOfModules.unit (scheme C).ringCatSheaf
  have h0 : Module.Finite K (SchemeModuleOpenSectionsOver (toBase C) O ⊤) :=
    (integralProper_originalGlobalFunctions_field_and_unitSectionsFinite (toBase C)).2
  let A := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  letI : EnoughInjectives A.Modules := sheafOfModules_enoughInjectives A.ringCatSheaf
  letI : HasExt.{u} A.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} A.Modules
  have h1 : Module.Finite K (schemeModuleCohomology (scheme C) O 1) :=
    selectedProjectivePrimeComponent_unitH1_finite_of_eventually_ownPositivePullback_vanishes
      p q hp hp0 n hq hnot C hIC hprime P
      (homogeneousIdeal_eventually_ownPositivePullback_cohomology_one_subsingleton C)
  have hstart : Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
      (positiveSheafOfModules (grading C) 0) ⊤) ∧
      Module.Finite K (schemeModuleCohomology (scheme C)
        (positiveSheafOfModules (grading C) 0) 1) := by
    let e : positiveSheafOfModules (grading C) 0 ≅ O :=
      positiveZeroTwistIso (grading C) ≪≫ (unitIsoZeroTwist (grading C)).symm
    letI : Module.Finite K (SchemeModuleOpenSectionsOver (toBase C) O ⊤) := h0
    letI : Module.Finite K (schemeModuleCohomology (scheme C) O 1) := h1
    exact ⟨Module.Finite.equiv (schemeModuleOpenTopIsoLinearEquivOver (toBase C) e).symm,
      Module.Finite.equiv (ownCoordinateCohomologyIsoLinearEquiv (toBase C) e 1).symm⟩
  intro m
  induction m with
  | zero => exact hstart
  | succ m hm =>
      have h := selectedProjectivePrimeComponent_ownPositiveCoordinate_finite_and_nativeEuler_step
        p q hp hp0 n hq hnot C hIC hprime P j hj m hm.1 hm.2
      exact ⟨h.1, h.2.1⟩

/-- The SAME native H0-H1 increment now has original geometric inputs only:
both finite-rank induction hypotheses are discharged by the preceding
original-input construction. The exact actual cokernel rank is retained. -/
theorem selectedProjectivePrimeComponent_ownPositiveCoordinate_nativeEuler_step_original
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) [HasExt.{u} (scheme C).Modules]
    (m : ℕ) :
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    let L := positiveSheafOfModules (grading C) m
    let M := positiveSheafOfModules (grading C) (m + 1)
    let Q := cokernel (ownPositiveCoordinateMultiplication C j m)
    ((Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) M ⊤) : ℤ) -
      Module.finrank K (schemeModuleCohomology (scheme C) M 1) =
      (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) L ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology (scheme C) L 1) +
        Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) Q ⊤)) := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  have hm := selectedProjectivePrimeComponent_ownPositiveTwist_hZero_hOne_finite_native
    p q hp hp0 n hq hnot C hIC hprime P j hj m
  exact (selectedProjectivePrimeComponent_ownPositiveCoordinate_finite_and_nativeEuler_step
    p q hp hp0 n hq hnot C hIC hprime P j hj m hm.1 hm.2).2.2

end PfaffianDescent.Coray
