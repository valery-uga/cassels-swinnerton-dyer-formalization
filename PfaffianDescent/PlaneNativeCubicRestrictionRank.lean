import PfaffianDescent.PlaneCubicPositiveRestrictionTerms
import PfaffianDescent.PlaneNativeIntrinsicCohomologyVanishing
import PfaffianDescent.PlaneHomogeneousGlobalSectionsLinear
import PfaffianDescent.PlaneNegativeTwistGlobalH0
import PfaffianDescent.FiniteFiveTermLinearRank
/-! SOURCE ONLY / UNCHECKED. Original-coefficient native ambient restriction
sequence derives genuine finite pushforward H0 of rank3d and zero H1.
No grade-as-H0 or Euler certificate appears in the geometric endpoints. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open ProjectiveNegativeTwist Coray AllCharacteristics.HomogeneousProjective
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Bounded generic original-field LES cut. The geometric callers below
construct their actual sequence and finite/vanishing inputs internally. -/
theorem nativeShortExact_rightTop_finite_rank_of_left_h1_zero
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) →
    Subsingleton (schemeModuleCohomology X S.X₁ 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) +
        Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) =
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hA hB hA1
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := hA
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) := hB
  letI : Subsingleton (schemeModuleCohomology X S.X₁ 1) := hA1
  letI : Mono S.f := hS.mono_f
  let f := schemeModuleOpenTopCoefficientLinearMapOver pi S.f
  let g := schemeModuleOpenTopCoefficientLinearMapOver pi S.g
  have hf : Function.Injective f := schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono pi S.f
  have hfg := schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS
  have hgb := (schemeModuleOpenTopConnectingLinearMaps_exact pi S hS).1
  have hg : Function.Surjective g := by
    intro z
    exact (hgb z).mp (Subsingleton.elim _ _)
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) := Module.Finite.of_surjective g hg
  have hdim := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hg, finrank_top,
    hfg.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf] at hdim
  exact ⟨inferInstance, hdim⟩

def planeCubicAmbientLeftRank (d : ℕ) : ℕ :=
  if 3 ≤ d then (d - 3 + 2).choose 2 else 0

/-- Exact genuine ambient plane monomial difference, including degrees1/2. -/
theorem planeCubicAmbient_choose_balance (d : ℕ) (hd : 1 ≤ d) :
    (d + 2).choose 2 = planeCubicAmbientLeftRank d + 3 * d := by
  by_cases h3 : 3 ≤ d
  · rw [planeCubicAmbientLeftRank, if_pos h3]
    have h := Coray.planeCubic_choose_difference (d - 3)
    have h5 : d - 3 + 5 = d + 2 := by omega
    have h3' : d - 3 + 3 = d := Nat.sub_add_cancel h3
    rw [h5, h3'] at h
    exact h
  · have hsmall : d = 1 ∨ d = 2 := by omega
    rcases hsmall with rfl | rfl <;>
      norm_num [planeCubicAmbientLeftRank, Nat.choose]

/-- SAME actual left coefficient object and original ambient scalar action. -/
theorem planeCubicPositiveRestriction_first_native_data
    [HasExt.{u} (Proj PS).Modules]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) (hd : 1 ≤ d) :
    let S := planeCubicPositiveRestrictionSequence F hF d
    Module.Finite K (SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3)) S.X₁ ⊤) ∧
      Subsingleton (schemeModuleCohomology (Proj PS) S.X₁ 1) ∧
      Subsingleton (schemeModuleCohomology (Proj PS) S.X₁ 2) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3)) S.X₁ ⊤) =
        planeCubicAmbientLeftRank d := by
  dsimp only
  by_cases h3 : 3 ≤ d
  · rw [planeCubicPositiveRestrictionSequence_first_of_three_le F hF d h3]
    have h0 := p2PositiveTwistTopSections_finite_finrank K (d - 3)
    have hc := p2_positiveTwist_cohomology_one_and_two_subsingleton K (d - 3)
    exact ⟨h0.1, hc.1, hc.2, by simpa only [planeCubicAmbientLeftRank, if_pos h3] using h0.2⟩
  · have hlt : d < 3 := Nat.lt_of_not_ge h3
    rw [planeCubicPositiveRestrictionSequence_first_of_lt_three F hF d hlt]
    have hm : 3 - d ≤ 2 := planeCubicPositiveRestrictionSequence_low_negative_degree_bound d hd
    have hm0 : 0 < 3 - d := by omega
    have hc := p2_negativeTwist_cohomology_one_and_two_subsingleton_of_le_two K (3 - d) hm
    letI : Subsingleton (SchemeModuleOpenSectionsOver
        (ambientToBase (R := K) (σ := Fin 3)) (sheafOfModules PS (3 - d)) ⊤) :=
      p2_negativeTwist_topSections_subsingleton_of_pos K
        (ambientToBase (R := K) (σ := Fin 3)) (3 - d) hm0
    exact ⟨inferInstance, hc.1, hc.2, by
      rw [Module.finrank_zero_of_subsingleton]
      simp only [planeCubicAmbientLeftRank, if_neg h3]⟩

/-- Ambient H1 of the actual closed pushforward O_E(d) is zero for d≥1. -/
theorem planeCubicPositivePushforward_cohomology_one_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) (hd : 1 ≤ d) :
    Subsingleton (schemeModuleCohomology (Proj PS)
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) d)) 1) := by
  let S := planeCubicPositiveRestrictionSequence F hF d
  have hA := planeCubicPositiveRestriction_first_native_data K F hF d hd
  have hB : Subsingleton (schemeModuleCohomology (Proj PS) S.X₂ 1) := by
    rw [planeCubicPositiveRestrictionSequence_middle F hF d]
    exact (p2_positiveTwist_cohomology_one_and_two_subsingleton K d).1
  letI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₁ 2) := hA.2.2.1
  letI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₂ 1) := hB
  have h := schemeModuleCohomology_one_subsingleton_of_middle_one_and_left_two
    (Proj PS) S (planeCubicPositiveRestrictionSequence_shortExact F hF hF0 d)
  simpa only [S, planeCubicPositiveRestrictionSequence_quotient F hF d] using h

/-- Genuine finite native pushforward H0 has rank3d, from its actual
restriction sequence and ORIGINAL ambient scalar action, not a grade premise. -/
theorem planeCubicPositivePushforward_topSections_finite_finrank
    [HasExt.{u} (Proj PS).Modules]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) (hd : 1 ≤ d) :
    Module.Finite K (SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3))
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) d)) ⊤) ∧
    Module.finrank K (SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3))
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) d)) ⊤) = 3 * d := by
  letI : Linear K (Proj PS).Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 3))
  let S := planeCubicPositiveRestrictionSequence F hF d
  have hA := planeCubicPositiveRestriction_first_native_data K F hF d hd
  have hB : Module.Finite K (SchemeModuleOpenSectionsOver
      (ambientToBase (R := K) (σ := Fin 3)) S.X₂ ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver
        (ambientToBase (R := K) (σ := Fin 3)) S.X₂ ⊤) = (d + 2).choose 2 := by
    rw [planeCubicPositiveRestrictionSequence_middle F hF d]
    exact p2PositiveTwistTopSections_finite_finrank K d
  have h := nativeShortExact_rightTop_finite_rank_of_left_h1_zero K
    (ambientToBase (R := K) (σ := Fin 3)) S
    (planeCubicPositiveRestrictionSequence_shortExact F hF hF0 d) hA.1 hB.1 hA.2.1
  have hdim := h.2
  rw [hA.2.2.2, hB.2, planeCubicAmbient_choose_balance d hd] at hdim
  have hdim' : Module.finrank K (SchemeModuleOpenSectionsOver
      (ambientToBase (R := K) (σ := Fin 3)) S.X₃ ⊤) = 3 * d := by omega
  have hResult :
      Module.Finite K (SchemeModuleOpenSectionsOver
        (ambientToBase (R := K) (σ := Fin 3)) S.X₃ ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver
        (ambientToBase (R := K) (σ := Fin 3)) S.X₃ ⊤) = 3 * d :=
    ⟨h.1, hdim'⟩
  have hQ : S.X₃ =
      (Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) d) :=
    planeCubicPositiveRestrictionSequence_quotient F hF d
  exact (congrArg (fun N : (Proj PS).Modules =>
    Module.Finite K (SchemeModuleOpenSectionsOver
      (ambientToBase (R := K) (σ := Fin 3)) N ⊤) ∧
    Module.finrank K (SchemeModuleOpenSectionsOver
      (ambientToBase (R := K) (σ := Fin 3)) N ⊤) = 3 * d) hQ).mp hResult

end PfaffianDescent.ProjectivePlaneNative
