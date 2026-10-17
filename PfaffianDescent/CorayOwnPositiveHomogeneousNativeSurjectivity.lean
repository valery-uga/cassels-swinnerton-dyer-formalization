import PfaffianDescent.CorayOriginalAmbientPolynomialPositiveRestriction
import PfaffianDescent.CorayOwnAmbientIdealEventuallyHOne
import PfaffianDescent.SheafModuleOverExtComparison

/-! SOURCE ONLY. Genuine eventual surjectivity of the EXISTING canonical
OWN grade-to-native-H0 map; every vanishing/quotient comparison is derived. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open BundleSectionZeroLocus IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal ambient polynomial restriction lifts every native quotient
section when its original ideal H1 vanishes. The ambient dictionary and
actual positive ideal ShortExact sequence are constructed inside the proof. -/
theorem originalAmbientHomogeneousRestriction_surjective_of_ideal_hOne_zero
    [hExt : HasExt.{u} (Proj PS).Modules] (I : HomogeneousIdeal PS)
    (m : ℕ) (hm : 0 < m)
    [Subsingleton (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m)) 1)] :
    Function.Surjective (p3ClosedImmersionHomogeneousRestrictionLinearMap
      (quotientProjMap I) m) := by
  let T := positiveSheafOfModules PS m
  let S := closedImmersionIdealTwistSequence (quotientProjMap I) T
  let e := schemeModuleTensorUnitLeftIso T
  have hS : S.ShortExact := by
    apply closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
      (quotientProjMap I) (p3StandardOpenLifted (K := K)) (p3StandardOpenLifted_coversTop K)
    intro i
    exact overFunctorIsoUnit_of_restrictIsoUnit (p3StandardOpen (K := K) i.down)
      (p3PositiveTwistStandardOpenIsoUnit K i.down m hm)
  letI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₁ 1) :=
    (inferInstance : Subsingleton (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m)) 1))
  intro z
  obtain ⟨f, hf⟩ := hom_postcomp_surjective_of_ext_one_subsingleton
    (show (Proj PS).Modules from SheafOfModules.unit (Proj PS).ringCatSheaf) S hS z
  obtain ⟨a, ha⟩ := p3HomogeneousGlobalSectionLinearMap_surjective K m hm (f ≫ e.hom)
  refine ⟨a, ?_⟩
  change p3HomogeneousGlobalSectionLinearMap K m a ≫ (e.inv ≫ S.g) = z
  calc
    _ = (f ≫ e.hom) ≫ (e.inv ≫ S.g) := congrArg (fun v => v ≫ (e.inv ≫ S.g)) ha
    _ = f ≫ S.g := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = z := hf

/-- The canonical quotient grade section is surjective under the SAME
original ideal H1 condition. Actual ambient polynomial lifting and the
proved canonical coefficient square give this, with no new section map. -/
theorem originalPositiveHomogeneousGlobalSectionLinearMap_surjective_of_ideal_hOne_zero
    [hExt : HasExt.{u} (Proj PS).Modules] (I : HomogeneousIdeal PS)
    (m : ℕ) (hm : 0 < m)
    [Subsingleton (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m)) 1)] :
    Function.Surjective (positiveHomogeneousGlobalSectionLinearMap I m) := by
  let i := quotientProjMap I
  let G := Scheme.Modules.pushforward i
  let q := closedImmersionUnitToPushforwardUnit i
  let e := originalAmbientPositiveTensorQuotientIso I m hm
  intro s
  obtain ⟨a, ha⟩ := originalAmbientHomogeneousRestriction_surjective_of_ideal_hOne_zero I m hm
    ((q ≫ G.map s) ≫ e.inv)
  refine ⟨⟨Ideal.Quotient.mk I.toIdeal a, (quotientGradedRingHom I).map_mem a.property⟩, ?_⟩
  apply nativeUnitSectionPushforward_injective i (positiveSheafOfModules (grading I) m)
  calc
    _ = p3ClosedImmersionHomogeneousRestrictionLinearMap i m a ≫ e.hom :=
      (originalAmbientPolynomialRestriction_comp_tensorQuotientIso I m hm a).symm
    _ = ((q ≫ G.map s) ≫ e.inv) ≫ e.hom := congrArg (fun v => v ≫ e.hom) ha
    _ = q ≫ G.map s := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Genuine eventual surjectivity for EVERY whole original homogeneous
ideal, including nonreduced and reducible schemes, over the original field.
The caller supplies no H1 vanishing, lifting, frame or graded=H0 premise. -/
theorem homogeneousIdeal_eventually_positiveHomogeneousGlobalSectionLinearMap_surjective
    [hExt : HasExt.{u} (Proj PS).Modules] (I : HomogeneousIdeal PS) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Function.Surjective (positiveHomogeneousGlobalSectionLinearMap I m) := by
  obtain ⟨B, hB⟩ := homogeneousIdeal_eventually_actualIdealTwist_cohomology_one_subsingleton I
  refine ⟨max B 1, fun m hm => ?_⟩
  have hmB : B ≤ m := (Nat.le_max_left B 1).trans hm
  have hmpos : 0 < m := (Nat.lt_add_one 0).trans_le ((Nat.le_max_right B 1).trans hm)
  letI : Subsingleton (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m)) 1) := hB m hmB
  exact originalPositiveHomogeneousGlobalSectionLinearMap_surjective_of_ideal_hOne_zero I m hmpos

end PfaffianDescent.Coray
