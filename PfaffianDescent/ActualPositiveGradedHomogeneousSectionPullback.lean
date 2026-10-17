import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullbackHom
import PfaffianDescent.SchemeModuleGlobalSectionsTop
import PfaffianDescent.ActualAmbientPositiveTwistQuotientIso

/- SOURCE ONLY / UNVERIFIED. The ACTUAL graded pullback adjunct carries
actual homogeneous global sections to their actual graded images.
This proves the section square rather than supplying it as a certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {A B R S : Type u} [CommRing A] [CommRing B]
  [SetLike R A] [AddSubgroupClass R A]
  [SetLike S B] [AddSubgroupClass S B]
  (G : ℕ → R) (H : ℕ → S) [GradedRing G] [GradedRing H]

lemma actualPositiveGradedHomogeneousSection_pushforward
    (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f)
    (m : ℕ) (a : G m) :
    (positiveSheafOfModules G m).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous G m a) ≫
      gradedRingHomPositiveTwistToPushforward G H f hf m =
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Proj.map f hf) ≫
      (Scheme.Modules.pushforward (Proj.map f hf)).map
        ((positiveSheafOfModules H m).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous H m ⟨f a, f.2 a.property⟩)) := by
  let g := Proj.map f hf
  let TG := positiveSheafOfModules G m
  let TH := positiveSheafOfModules H m
  let N := (Scheme.Modules.pushforward g).obj TH
  let sG := positiveGlobalSectionOfHomogeneous G m a
  let sH := positiveGlobalSectionOfHomogeneous H m ⟨f a, f.2 a.property⟩
  let b := gradedRingHomPositiveTwistToPushforward G H f hf m
  have hLeft : N.unitHomEquiv (TG.unitHomEquiv.symm sG ≫ b) =
      SheafOfModules.sectionsMap b sG :=
    (SheafOfModules.unitHomEquiv_comp_apply (TG.unitHomEquiv.symm sG) b).trans
      (congrArg (SheafOfModules.sectionsMap b) (TG.unitHomEquiv.apply_symm_apply sG))
  have hRight : N.unitHomEquiv
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit g ≫
        (Scheme.Modules.pushforward g).map (TH.unitHomEquiv.symm sH)) =
      SheafOfModules.pushforwardSections g.toRingCatSheafHom sH :=
    (SheafOfModules.pushforwardSections_unitHomEquiv
      g.toRingCatSheafHom (TH.unitHomEquiv.symm sH)).symm.trans
      (congrArg (SheafOfModules.pushforwardSections g.toRingCatSheafHom)
        (TH.unitHomEquiv.apply_symm_apply sH))
  have hTop : schemeModuleSectionsEquivTop N (SheafOfModules.sectionsMap b sG) =
      schemeModuleSectionsEquivTop N
        (SheafOfModules.pushforwardSections g.toRingCatSheafHom sH) := by
    apply Subtype.ext
    funext y
    letI : (positivePointIdeal G (Proj.map f hf y.1)).IsPrime :=
      ProjectiveSpectrum.isPrime (Proj.map f hf y.1)
    letI : (positivePointIdeal H y.1).IsPrime :=
      ProjectiveSpectrum.isPrime y.1
    change Localization.localRingHom
        (positivePointIdeal G (Proj.map f hf y.1)) (positivePointIdeal H y.1)
        f.toRingHom rfl
        (Localization.mk (a : A) (1 : (positivePointIdeal G (Proj.map f hf y.1)).primeCompl)) =
      Localization.mk (f a : B) (1 : (positivePointIdeal H y.1).primeCompl)
    rw [Localization.localRingHom_mk]
    congr 1
    apply Subtype.ext
    exact f.toRingHom.map_one
  apply (N.unitHomEquiv.trans (schemeModuleSectionsEquivTop N)).injective
  exact ((congrArg (schemeModuleSectionsEquivTop N) hLeft).trans hTop).trans
    (congrArg (schemeModuleSectionsEquivTop N) hRight).symm

lemma actualPositiveGradedHomogeneousSection_pullback
    (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f)
    (m : ℕ) (a : G m) :
    letI := BundleSectionZeroLocus.isIso_pullbackUnitComparison (Proj.map f hf)
    inv (BundleSectionZeroLocus.pullbackUnitComparison (Proj.map f hf)) ≫
      (Scheme.Modules.pullback (Proj.map f hf)).map
        ((positiveSheafOfModules G m).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous G m a)) ≫
      cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom G H f hf m =
    (positiveSheafOfModules H m).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous H m ⟨f a, f.2 a.property⟩) := by
  let g := Proj.map f hf
  letI := BundleSectionZeroLocus.isIso_pullbackUnitComparison g
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let s := (positiveSheafOfModules G m).unitHomEquiv.symm
    (positiveGlobalSectionOfHomogeneous G m a)
  let t := (positiveSheafOfModules H m).unitHomEquiv.symm
    (positiveGlobalSectionOfHomogeneous H m ⟨f a, f.2 a.property⟩)
  have hu : (adj.homEquiv _ _).symm
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit g) =
        BundleSectionZeroLocus.pullbackUnitComparison g := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      g.toRingCatSheafHom).symm
  have h := congrArg (fun v => (adj.homEquiv _ _).symm v)
    (actualPositiveGradedHomogeneousSection_pushforward G H f hf m a)
  rw [adj.homEquiv_naturality_left_symm,
    adj.homEquiv_naturality_right_symm, hu] at h
  change inv (BundleSectionZeroLocus.pullbackUnitComparison g) ≫
    ((Scheme.Modules.pullback g).map s ≫
      (adj.homEquiv _ _).symm (gradedRingHomPositiveTwistToPushforward G H f hf m)) = t
  rw [h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

lemma actualAmbientPositiveTwistQuotientIso_homogeneousSection
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (m : ℕ) (a : MvPolynomial.homogeneousSubmodule (Fin 4) K m) :
    letI := BundleSectionZeroLocus.isIso_pullbackUnitComparison (quotientProjMap I)
    inv (BundleSectionZeroLocus.pullbackUnitComparison (quotientProjMap I)) ≫
      (Scheme.Modules.pullback (quotientProjMap I)).map
        ((positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 4) K) m a)) ≫
      (actualAmbientPositiveTwistQuotientIso I m).hom =
    (positiveSheafOfModules (grading I) m).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading I) m
        ⟨Ideal.Quotient.mk I.toIdeal a, (quotientGradedRingHom I).2 a.property⟩) :=
  actualPositiveGradedHomogeneousSection_pullback
    (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading I)
    (quotientGradedRingHom I) (irrelevant_le_map_quotientGradedRingHom I) m a

end PfaffianDescent
