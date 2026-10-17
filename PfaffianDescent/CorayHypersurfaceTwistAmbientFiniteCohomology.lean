import PfaffianDescent.VoisinHypersurfaceTwist
import PfaffianDescent.VoisinGlobalExtVanishing
import PfaffianDescent.P3GeneralNegativeTwistTopResidueGroundLinear

/-! Original-K linear connecting injections for the ACTUAL all-m ambient
hypersurface restriction sequence. Actual pushed-forward negative twists
have zero ambient H¹ and finite ambient H². No intrinsic hypersurface/curve
comparison, scalar action or finiteness conclusion is assumed.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]

/-- The genuine connecting class of an ACTUAL short exact sequence induces
a linear map for the independently original pi-defined Ext actions. -/
def schemeModuleRestrictionConnectingLinearMapOver
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    schemeModuleCohomology X S.X₃ n →ₗ[K]
      schemeModuleCohomology X S.X₁ (n + 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact Ext.postcompOfLinear hS.extClass K
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) rfl

/-- Vanishing of the ACTUAL middle cohomology makes the ACTUAL connecting
map injective, by the genuine Ext long exact sequence. This general helper
retains natural short-exactness/vanishing inputs; geometric callers derive them. -/
theorem schemeModuleRestrictionConnectingLinearMapOver_injective
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (schemeModuleCohomology X S.X₂ n)] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Function.Injective (schemeModuleRestrictionConnectingLinearMapOver pi S hS n) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  apply (injective_iff_map_eq_zero
    (schemeModuleRestrictionConnectingLinearMapOver pi S hS n)).mpr
  intro z hz
  have hc : z.comp hS.extClass (show n + 1 = n + 1 by rfl) = 0 := hz
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) hS z rfl hc
  rw [← ha, show a = 0 from Subsingleton.elim _ _]
  exact Ext.zero_comp (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    n (Ext.mk₀ S.g) n (add_zero n)

/-- Finite next-left cohomology and zero middle cohomology imply finite
right cohomology, with the independently ORIGINAL pi action throughout. -/
theorem schemeModuleRestriction_rightCohomology_finite_of_middle_zero_and_next_left_finite
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (schemeModuleCohomology X S.X₂ n)] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (schemeModuleCohomology X S.X₁ (n + 1)) →
      Module.Finite K (schemeModuleCohomology X S.X₃ n) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hfinite
  letI : Module.Finite K (schemeModuleCohomology X S.X₁ (n + 1)) := hfinite
  exact FiniteDimensional.of_injective
    (schemeModuleRestrictionConnectingLinearMapOver pi S hS n)
    (schemeModuleRestrictionConnectingLinearMapOver_injective pi S hS n)

end PfaffianDescent.Coray

namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- ALL actual pushed-forward hypersurface negative twists have zero
ambient H¹; the all-m ambient vanishings and actual sequence are internal. -/
theorem p3HypersurfaceTwistPushforward_cohomology_one_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] (m : ℕ) :
    Subsingleton (schemeModuleCohomology (Proj PS)
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) m)) 1) := by
  let S := hypersurfaceTwistRestrictionSequence p hp m
  letI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₂ 1) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K m).1
  letI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₁ 2) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K (m + d)).2
  exact schemeModuleCohomology_one_subsingleton_of_middle_one_and_left_two
    (Proj PS) S (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 m)

/-- The ACTUAL connecting map embeds ambient H² of the ACTUAL pushed-forward
hypersurface twist into H³(O(-(m+d))), linearly for the ORIGINAL ambient pi. -/
theorem p3HypersurfaceTwistPushforward_connecting_two_injective
    [HasExt.{u} (Proj PS).Modules]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] (m : ℕ) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Function.Injective (Coray.schemeModuleRestrictionConnectingLinearMapOver
      (ambientToBase (R := K) (σ := Fin 4)) (hypersurfaceTwistRestrictionSequence p hp m)
      (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 m) 2) := by
  let S := hypersurfaceTwistRestrictionSequence p hp m
  letI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₂ 2) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K m).2
  exact Coray.schemeModuleRestrictionConnectingLinearMapOver_injective
    (ambientToBase (R := K) (σ := Fin 4)) S
    (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 m) 2

/-- Finite ambient H² of EVERY actual pushed-forward negative hypersurface
twist, derived from the actual original-K finite ambient H³ producer. -/
theorem p3HypersurfaceTwistPushforward_cohomology_two_finite
    [HasExt.{u} (Proj PS).Modules]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] (m : ℕ) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology (Proj PS)
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) m)) 2) := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  let S := hypersurfaceTwistRestrictionSequence p hp m
  letI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₂ 2) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K m).2
  have hfinite : Module.Finite K (schemeModuleCohomology (Proj PS) S.X₁ 3) :=
    p3NegativeTwist_cohomology_three_finite_over_ambient_base K (m + d)
  exact Coray.schemeModuleRestriction_rightCohomology_finite_of_middle_zero_and_next_left_finite
    (ambientToBase (R := K) (σ := Fin 4)) S
    (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 m) 2 hfinite

end PfaffianDescent.ProjectiveNegativeTwist
