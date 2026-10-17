import PfaffianDescent.ActualPositiveGradedHomogeneousSectionPullback
import PfaffianDescent.ActualP3HomogeneousSectionUnitHom
import PfaffianDescent.ActualP3IdealHomogeneousRestrictionKernel
import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear
import PfaffianDescent.CorayCartierCanonicalProjectionFormula
import PfaffianDescent.VoisinPositiveTwistTriviality

/-! SOURCE ONLY. Original ambient polynomial restriction and actual quotient
coefficient Iso; all squares are proved for the literal original maps. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open BundleSectionZeroLocus IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pushforward of an actual unit section is injective for ANY morphism.
The actual pullback-unit comparison and adjunction derive the assertion. -/
theorem nativeUnitSectionPushforward_injective
    {X Y : Scheme.{u}} (i : Y ⟶ X) (M : Y.Modules) :
    Function.Injective (fun s : SheafOfModules.unit Y.ringCatSheaf ⟶ M =>
      closedImmersionUnitToPushforwardUnit i ≫ (Scheme.Modules.pushforward i).map s) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction i
  letI : IsIso (pullbackUnitComparison i) := isIso_pullbackUnitComparison i
  have hu : (adj.homEquiv _ _).symm (closedImmersionUnitToPushforwardUnit i) =
      pullbackUnitComparison i := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      i.toRingCatSheafHom).symm
  intro s t h
  have h' := congrArg (fun v => (adj.homEquiv _ _).symm v) h
  rw [adj.homEquiv_naturality_right_symm,
    adj.homEquiv_naturality_right_symm, hu] at h'
  exact (cancel_epi (pullbackUnitComparison i)).mp h'

/-- The existing canonical grade-to-H0 map is the actual homogeneous unit
section, with the existing original field action. -/
lemma originalPositiveHomogeneousGlobalSectionLinearMap_unitHom
    (I : HomogeneousIdeal PS) (m : ℕ) (a : grading I m) :
    positiveHomogeneousGlobalSectionLinearMap I m a =
      (positiveSheafOfModules (grading I) m).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) m a) := by
  change (positiveSheafOfModules (grading I) m).unitHomEquiv.symm
      ((schemeModuleSectionsEquivTop (positiveSheafOfModules (grading I) m)).symm
        ((schemeModuleSectionsEquivTop (positiveSheafOfModules (grading I) m))
          (positiveGlobalSectionOfHomogeneous (grading I) m a))) = _
  rw [Equiv.symm_apply_apply]

private theorem rawAmbientPositiveTwist_locallyRankOne
    (m : ℕ) (hm : 0 < m) :
    schemeModuleLocallyRankOne (positiveSheafOfModules PS m) := by
  intro x
  have hx : x ∈ (⨆ i : P3CoordinateIndex.{u}, p3StandardOpenLifted (K := K) i) := by
    rw [p3StandardOpenLifted_iSup K]
    trivial
  obtain ⟨i, hix⟩ := Opens.mem_iSup.mp hx
  let U := p3StandardOpenLifted (K := K) i
  let T := positiveSheafOfModules PS m
  let O : (Proj PS).Modules := SheafOfModules.unit (Proj PS).ringCatSheaf
  let eT := overFunctorIsoUnit_of_restrictIsoUnit.{u}
    (X := Proj PS) (T := T) (p3StandardOpen (K := K) i.down)
    (p3PositiveTwistStandardOpenIsoUnit K i.down m hm)
  let eO := PfaffianDescent.SheafOfModules.overFunctor_globalUnitIso U (Iso.refl O)
  exact ⟨U, hix, ⟨eT ≪≫ eO.symm⟩⟩

/-- The ORIGINAL tensor quotient identifies with pushforward of the OWN
positive twist by the canonical fiber projection and actual graded adjunct. -/
def originalAmbientPositiveTensorQuotientIso
    (I : HomogeneousIdeal PS) (m : ℕ) (hm : 0 < m) :
    (closedImmersionIdealTwistSequence (quotientProjMap I)
      (positiveSheafOfModules PS m)).X₃ ≅
        (Scheme.Modules.pushforward (quotientProjMap I)).obj
          (positiveSheafOfModules (grading I) m) := by
  let i := quotientProjMap I
  let T := positiveSheafOfModules PS m
  letI : IsIso (schemeModuleCanonicalFiberProjection i T) :=
    schemeModuleCanonicalFiberProjection_isIso_of_locallyRankOne i T
      (rawAmbientPositiveTwist_locallyRankOne m hm)
  exact asIso (schemeModuleCanonicalFiberProjection i T) ≪≫
    (Scheme.Modules.pushforward i).mapIso (actualAmbientPositiveTwistQuotientIso I m)

/-- Whole original restriction followed by that actual Iso is the SAME
graded quotient positive restriction, by the original adjunction square. -/
theorem originalAmbientPositiveRestriction_comp_tensorQuotientIso
    (I : HomogeneousIdeal PS) (m : ℕ) (hm : 0 < m) :
    p3ClosedImmersionPositiveRestriction (quotientProjMap I) m ≫
      (originalAmbientPositiveTensorQuotientIso I m hm).hom =
    gradedRingHomPositiveTwistToPushforward PS (grading I)
      (quotientGradedRingHom I) (irrelevant_le_map_quotientGradedRingHom I) m := by
  let i := quotientProjMap I
  let T := positiveSheafOfModules PS m
  let e := schemeModuleTensorUnitLeftIso T
  let S := closedImmersionIdealTwistSequence i T
  let pr := schemeModuleCanonicalFiberProjection i T
  let c := (actualAmbientPositiveTwistQuotientIso I m).hom
  let G := Scheme.Modules.pushforward i
  have hp := schemeModuleCanonicalFiberProjection_unit_square i T
  change S.g ≫ pr = e.hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T at hp
  have hg : gradedRingHomPositiveTwistToPushforward PS (grading I)
      (quotientGradedRingHom I) (irrelevant_le_map_quotientGradedRingHom I) m =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T ≫ G.map c := by
    exact (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _).apply_symm_apply _).symm
  change (e.inv ≫ S.g) ≫ (pr ≫ G.map c) = _
  calc
    _ = e.inv ≫ (S.g ≫ pr) ≫ G.map c := by simp only [Category.assoc]
    _ = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T ≫ G.map c := by
      rw [hp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = _ := hg.symm

/-- The actual ambient polynomial restriction, after the genuine quotient
coefficient Iso, is the pushforward of the canonical ORIGINAL grade section.
No graded=H0 assertion or comparison square is supplied. -/
theorem originalAmbientPolynomialRestriction_comp_tensorQuotientIso
    (I : HomogeneousIdeal PS) (m : ℕ) (hm : 0 < m) (a : PS m) :
    p3ClosedImmersionHomogeneousRestrictionLinearMap (quotientProjMap I) m a ≫
      (originalAmbientPositiveTensorQuotientIso I m hm).hom =
    closedImmersionUnitToPushforwardUnit (quotientProjMap I) ≫
      (Scheme.Modules.pushforward (quotientProjMap I)).map
        (positiveHomogeneousGlobalSectionLinearMap I m
          ⟨Ideal.Quotient.mk I.toIdeal a, (quotientGradedRingHom I).map_mem a.property⟩) := by
  change (p3HomogeneousGlobalSectionLinearMap K m a ≫
      p3ClosedImmersionPositiveRestriction (quotientProjMap I) m) ≫ _ = _
  rw [Category.assoc, originalAmbientPositiveRestriction_comp_tensorQuotientIso I m hm,
    p3HomogeneousGlobalSectionLinearMap_unitHom K m a,
    originalPositiveHomogeneousGlobalSectionLinearMap_unitHom]
  exact actualPositiveGradedHomogeneousSection_pushforward PS (grading I)
    (quotientGradedRingHom I) (irrelevant_le_map_quotientGradedRingHom I) m a

end PfaffianDescent.Coray
