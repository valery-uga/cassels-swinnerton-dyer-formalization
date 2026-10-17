import PfaffianDescent.CorayOwnAmbientIdealEventuallyHOne
import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact
import PfaffianDescent.VoisinPositiveTwistTriviality

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Actual top-section lifting through a genuine short exact coefficient
sequence, retaining the independently defined original base actions. -/
theorem schemeModuleOpenTopCoefficientLinearMapOver_surjective_of_left_hOne_zero
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Subsingleton (schemeModuleCohomology X S.X₁ 1)] :
    Function.Surjective (schemeModuleOpenTopCoefficientLinearMapOver pi S.g) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let E₂ := schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₂
  let E₃ := schemeModuleUnitHomGroundLinearEquivOpenTop pi S.X₃
  intro z
  obtain ⟨f, hf⟩ := hom_postcomp_surjective_of_ext_one_subsingleton
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) S hS (E₃.symm z)
  refine ⟨E₂ f, ?_⟩
  change S.g.val.app (Opposite.op ⊤) (E₂ f) = z
  have hImage : E₃ (f ≫ S.g) = z :=
    (congrArg (fun t => E₃ t) hf).trans (E₃.apply_symm_apply z)
  exact (schemeModuleUnitHomGroundLinearEquivOpenTop_naturality pi S.g f).symm.trans hImage

/-- Eventual SURJECTIVITY on actual top sections of the SAME ambient
ideal restriction sequence. This is obtained from the internally proved
whole-ideal H1 vanishing, not assumed as a graded/native H0 dictionary. -/
theorem homogeneousIdeal_eventually_actualTwistedQuotient_openTopRestriction_surjective
    [hExt : HasExt.{u} (Proj PS).Modules]
    (pi : Proj PS ⟶ Spec (CommRingCat.of K)) (I : HomogeneousIdeal PS) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Function.Surjective (schemeModuleOpenTopCoefficientLinearMapOver pi
        (closedImmersionIdealTwistSequence (quotientProjMap I)
          (positiveSheafOfModules PS m)).g) := by
  obtain ⟨B, hB⟩ := homogeneousIdeal_eventually_actualIdealTwist_cohomology_one_subsingleton I
  refine ⟨max B 1, fun m hm => ?_⟩
  have hmB : B ≤ m := (Nat.le_max_left B 1).trans hm
  have hmpos : 0 < m := (Nat.lt_add_one 0).trans_le ((Nat.le_max_right B 1).trans hm)
  let T := positiveSheafOfModules PS m
  let S := closedImmersionIdealTwistSequence (quotientProjMap I) T
  have hS : S.ShortExact := by
    apply closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
      (quotientProjMap I) (p3StandardOpenLifted (K := K)) (p3StandardOpenLifted_coversTop K)
    intro i
    exact overFunctorIsoUnit_of_restrictIsoUnit (p3StandardOpen (K := K) i.down)
      (p3PositiveTwistStandardOpenIsoUnit K i.down m hmpos)
  letI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₁ 1) := hB m hmB
  exact schemeModuleOpenTopCoefficientLinearMapOver_surjective_of_left_hOne_zero pi S hS

end PfaffianDescent.Coray
