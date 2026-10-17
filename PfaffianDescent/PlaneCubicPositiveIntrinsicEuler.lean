import PfaffianDescent.PlaneNativeCubicRestrictionRank
import PfaffianDescent.ClosedImmersionCohomologyOneLinearInjection
/-! SOURCE ONLY / UNCHECKED. Intrinsic χ(O_E(d))=3d for d≥1 on the SAME
native plane cubic with the independently original hypersurfaceToBase action.
No graded-piece/H0, pushforward/H1 or Euler certificate is a premise. -/
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

/-- Bounded original-action section transport for actual equal opens. -/
def nativeTopSectionOpenEqLinearEquiv
    {X : Scheme.{u}} (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (U V : X.Opens) (h : U = V) :
    SchemeModuleOpenSectionsOver pi M U ≃ₗ[K] SchemeModuleOpenSectionsOver pi M V := by
  subst V
  exact LinearEquiv.refl K _

/-- Equal original structure morphisms retain both independently given
scalar actions and induce the identity native section equivalence. -/
def nativeTopSectionBaseEqLinearEquiv
    {X : Scheme.{u}} (pi pi' : X ⟶ Spec (CommRingCat.of K))
    (h : pi = pi') (M : X.Modules) :
    SchemeModuleOpenSectionsOver pi M ⊤ ≃ₗ[K] SchemeModuleOpenSectionsOver pi' M ⊤ := by
  subst pi'
  exact LinearEquiv.refl K _

/-- Actual closed-pushforward native H0, with its original ambient action,
is equivalent to SAME intrinsic native H0 with its ORIGINAL cubic action. -/
def planeCubicPositivePushforwardTopSectionsLinearEquiv
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3))
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) d)) ⊤ ≃ₗ[K]
      SchemeModuleOpenSectionsOver (hypersurfaceToBase F hF)
        (positiveSheafOfModules (grading (equationIdeal F hF)) d) ⊤ := by
  let pi := ambientToBase (R := K) (σ := Fin 3)
  let f := hypersurfaceToAmbient F hF
  let M := positiveSheafOfModules (grading (equationIdeal F hF)) d
  let e₁ := schemeModulePushforward_openSectionsLinearEquiv pi f M ⊤
  let e₂ := nativeTopSectionOpenEqLinearEquiv K (f ≫ pi) M (f ⁻¹ᵁ ⊤) ⊤ (by simp)
  let e₃ := nativeTopSectionBaseEqLinearEquiv K (f ≫ pi) (hypersurfaceToBase F hF)
    (quotientProjMap_toBase (equationIdeal F hF)) M
  exact (e₁.trans e₂).trans e₃

/-- Original intrinsic native O_E(d) H1 vanishes through the actual closed
immersion map. The linear comparison's injectivity is internally proved. -/
theorem planeCubicPositiveIntrinsic_cohomology_one_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal F hF))]
    [HasExt.{u} (scheme (equationIdeal F hF)).Modules] (d : ℕ) (hd : 1 ≤ d) :
    Subsingleton (schemeModuleCohomology (scheme (equationIdeal F hF))
      (positiveSheafOfModules (grading (equationIdeal F hF)) d) 1) := by
  let pi := ambientToBase (R := K) (σ := Fin 3)
  let f : scheme (equationIdeal F hF) ⟶ Proj PS := hypersurfaceToAmbient F hF
  let M : (scheme (equationIdeal F hF)).Modules :=
    positiveSheafOfModules (grading (equationIdeal F hF)) d
  letI : Linear K (Proj PS).Modules := schemeModulesLinearOver pi
  letI : Linear K (scheme (equationIdeal F hF)).Modules := schemeModulesLinearOver (f ≫ pi)
  letI : Subsingleton (schemeModuleCohomology (Proj PS)
      ((Scheme.Modules.pushforward f).obj M) 1) :=
    planeCubicPositivePushforward_cohomology_one_subsingleton K F hF hF0 d hd
  have hInjective := closedImmersion_cohomologyOneLinearMap_injective.{u}
    (K := K) (X := scheme (equationIdeal F hF)) (Y := Proj PS) pi f M
  exact hInjective.subsingleton

/-- GENUINE original-action intrinsic top H0 rank3d and finiteness. The
coefficient is actual native O_E(d), not its homogeneous graded piece. -/
theorem planeCubicPositiveIntrinsic_topSections_finite_finrank
    [HasExt.{u} (Proj PS).Modules]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal F hF))] (d : ℕ) (hd : 1 ≤ d) :
    Module.Finite K (SchemeModuleOpenSectionsOver (hypersurfaceToBase F hF)
      (positiveSheafOfModules (grading (equationIdeal F hF)) d) ⊤) ∧
    Module.finrank K (SchemeModuleOpenSectionsOver (hypersurfaceToBase F hF)
      (positiveSheafOfModules (grading (equationIdeal F hF)) d) ⊤) = 3 * d := by
  have h := planeCubicPositivePushforward_topSections_finite_finrank K F hF hF0 d hd
  let e := planeCubicPositivePushforwardTopSectionsLinearEquiv K F hF d
  letI : Module.Finite K (SchemeModuleOpenSectionsOver (ambientToBase (R := K) (σ := Fin 3))
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient F hF)).obj
        (positiveSheafOfModules (grading (equationIdeal F hF)) d)) ⊤) := h.1
  refine ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, ?_⟩
  rw [← e.finrank_eq]
  exact h.2

/-- Literal χ(O_E(d))=3d for every d≥1, on the SAME actual native cubic
and SAME original scalar action. No Euler/rank/vanishing certificate premise. -/
theorem planeCubicPositiveIntrinsic_finite_euler_three_degree
    [HasExt.{u} (Proj PS).Modules]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal F hF))]
    [HasExt.{u} (scheme (equationIdeal F hF)).Modules] (d : ℕ) (hd : 1 ≤ d) :
    letI : Linear K (scheme (equationIdeal F hF)).Modules := schemeModulesLinearOver (hypersurfaceToBase F hF)
    Module.Finite K (SchemeModuleOpenSectionsOver (hypersurfaceToBase F hF)
      (positiveSheafOfModules (grading (equationIdeal F hF)) d) ⊤) ∧
    Module.Finite K (schemeModuleCohomology (scheme (equationIdeal F hF))
      (positiveSheafOfModules (grading (equationIdeal F hF)) d) 1) ∧
    ((Module.finrank K (SchemeModuleOpenSectionsOver (hypersurfaceToBase F hF)
      (positiveSheafOfModules (grading (equationIdeal F hF)) d) ⊤) : ℤ) -
      Module.finrank K (schemeModuleCohomology (scheme (equationIdeal F hF))
        (positiveSheafOfModules (grading (equationIdeal F hF)) d) 1)) = 3 * (d : ℤ) := by
  letI : Linear K (scheme (equationIdeal F hF)).Modules := schemeModulesLinearOver (hypersurfaceToBase F hF)
  have h0 := planeCubicPositiveIntrinsic_topSections_finite_finrank K F hF hF0 d hd
  letI : Subsingleton (schemeModuleCohomology (scheme (equationIdeal F hF))
      (positiveSheafOfModules (grading (equationIdeal F hF)) d) 1) :=
    planeCubicPositiveIntrinsic_cohomology_one_subsingleton K F hF hF0 d hd
  refine ⟨h0.1, inferInstance, ?_⟩
  rw [h0.2, Module.finrank_zero_of_subsingleton]
  simp

end PfaffianDescent.ProjectivePlaneNative
