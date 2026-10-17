import PfaffianDescent.VoisinFixedLinearSystemUniversalDescent

/-!
# Zero-ideal descent for the projective universal section

This file identifies the pullbacks of the chartwise universal zero ideals
on every overlap of the refined finite affine product cover.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchemeModuleFiniteFreeAffineCover

/-- Restriction-to-pullback followed by pullback composition on the left
overlap chart, before transport along equality of the surface maps. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftPreCongrModuleIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  let p := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  (Scheme.Modules.restrictFunctorIsoPullback p).app
      (C.projectiveSectionLocalModule base M ij) ≪≫
    (Scheme.Modules.pullbackComp p
      (C.projectiveSectionOpenCoverToSurface base M ij)).app M

/-- The canonical free presentation obtained by restricting the left chart
presentation to an overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftRestrictedFreeIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.restrictionFreeIsoOf
    (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl)) I
    (C.projectiveSectionLocalFreeIso base M ij)

/-- The module isomorphism induced by equality of the two overlap-to-surface
maps. -/
noncomputable def projectiveSectionOpenCoverOverlapPullbackCongrModuleIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)).app M

/-- The left free presentation before congruence of the overlap-to-surface
maps. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftPreCongrFreeIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  C.projectiveSectionOpenCoverOverlapLeftRestrictedFreeIso base M ij kl ≪≫
    C.projectiveSectionOpenCoverOverlapLeftPreCongrModuleIso base M ij kl

/-- The left free presentation in the common right-hand pullback module. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftCommonFreeIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  C.projectiveSectionOpenCoverOverlapLeftPreCongrFreeIso base M ij kl ≪≫
    C.projectiveSectionOpenCoverOverlapPullbackCongrModuleIso base M ij kl

/-- The canonical free presentation obtained by restricting the right chart
presentation to an overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapRightRestrictedFreeIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.restrictionFreeIsoOf
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl)) I
    (C.projectiveSectionLocalFreeIso base M kl)

/-- The right free presentation in the common pullback module. -/
noncomputable def projectiveSectionOpenCoverOverlapRightCommonFreeIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  C.projectiveSectionOpenCoverOverlapRightRestrictedFreeIso base M ij kl ≪≫
    C.projectiveSectionOpenCoverOverlapRightToCommonModuleIso base M ij kl

/-- A single common coordinate ideal on a refined overlap, using the left
restricted free presentation and the right-normalized common equation. -/
noncomputable def projectiveSectionOpenCoverOverlapCommonZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionOpenCoverOverlapLeftCommonFreeIso base M ij kl)
    (C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl)

/-
set_option backward.isDefEq.respectTransparency false in
/-- The left local ideal restricts to the common overlap ideal. -/
theorem projectiveSectionLocalZeroIdeal_comap_overlap_left
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroIdeal base M ij).comap
        (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) =
      C.projectiveSectionOpenCoverOverlapCommonZeroIdeal base M ij kl := by
  let pL := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  letI : IsAffine ((C.projectiveSectionOpenCover base M).X ij) :=
    C.projectiveSectionOpenCover_affine base M ij
  let eL := BundleSectionZeroLocus.restrictionFreeIsoOf pL I
    (C.projectiveSectionLocalFreeIso base M ij)
  let sL := C.projectiveSectionOpenCoverOverlapLeftRestrictedSection base M ij kl
  let L := C.projectiveSectionOpenCoverOverlapLeftPreCongrModuleIso base M ij kl
  let H := (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)).app M
  let tL₀ := C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
    base M ij kl
  let tL := C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl
  let tR := C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl
  let a := BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (C.projectiveSectionOpenCoverOverlapUnit base M ij kl)
  letI : IsIso a :=
    C.isIso_projectiveSectionOpenCoverOverlapUnitCoefficient base M ij kl
  unfold projectiveSectionLocalZeroIdeal
  change (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionLocalFreeIso base M ij)
    (C.projectiveSectionLocalUniversalSection base M ij)).comap pL = _
  rw [BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction
    pL I (C.projectiveSectionLocalFreeIso base M ij)
      (C.projectiveSectionLocalUniversalSection base M ij)]
  unfold projectiveSectionOpenCoverOverlapCommonZeroIdeal
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I eL sL =
        BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L)
          (SheafOfModules.sectionsMap L.hom sL) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq I eL L sL
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L) tL₀ := by
      have hp := C.projectiveSectionOpenCoverOverlap_left_preCongr_transport
        base M ij kl
      unfold projectiveSectionOpenCoverOverlapLeftPreCongrSection at hp
      exact congrArg
        (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L)) hp
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H)
          (SheafOfModules.sectionsMap H.hom tL₀) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
        I (eL ≪≫ L) H tL₀
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H) tL := by
      have hc := C.projectiveSectionOpenCoverOverlap_left_universal_congr
        base M ij kl
      unfold projectiveSectionOpenCoverOverlapLeftCongruentSection at hc
      exact congrArg
        (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H)) hc
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H)
          (BundleSectionZeroLocus.scaleSection a tR) := by
      rw [C.projectiveSectionOpenCoverOverlap_universalSection_commonScale
        base M ij kl]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H) tR :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso
        I (eL ≪≫ L ≪≫ H) a tR

set_option backward.isDefEq.respectTransparency false in
/-- The right local ideal restricts to the same common overlap ideal. -/
theorem projectiveSectionLocalZeroIdeal_comap_overlap_right
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroIdeal base M kl).comap
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) =
      C.projectiveSectionOpenCoverOverlapCommonZeroIdeal base M ij kl := by
  let pR := pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let pL := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  letI : IsAffine ((C.projectiveSectionOpenCover base M).X kl) :=
    C.projectiveSectionOpenCover_affine base M kl
  let eR := BundleSectionZeroLocus.restrictionFreeIsoOf pR I
    (C.projectiveSectionLocalFreeIso base M kl)
  let eL := BundleSectionZeroLocus.restrictionFreeIsoOf pL I
    (C.projectiveSectionLocalFreeIso base M ij)
  let R := C.projectiveSectionOpenCoverOverlapRightToCommonModuleIso base M ij kl
  let L := C.projectiveSectionOpenCoverOverlapLeftPreCongrModuleIso base M ij kl
  let H := (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)).app M
  let sR := C.projectiveSectionOpenCoverOverlapRightRestrictedSection base M ij kl
  let tR := C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl
  unfold projectiveSectionLocalZeroIdeal
  change (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionLocalFreeIso base M kl)
    (C.projectiveSectionLocalUniversalSection base M kl)).comap pR = _
  rw [BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction
    pR I (C.projectiveSectionLocalFreeIso base M kl)
      (C.projectiveSectionLocalUniversalSection base M kl)]
  unfold projectiveSectionOpenCoverOverlapCommonZeroIdeal
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I eR sR =
        BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eR ≪≫ R)
          (SheafOfModules.sectionsMap R.hom sR) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq I eR R sR
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eR ≪≫ R) tR := by
      have hr := C.projectiveSectionOpenCoverOverlap_right_section_transport
        base M ij kl
      unfold projectiveSectionOpenCoverOverlapRightTransportedSection at hr
      exact congrArg
        (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eR ≪≫ R)) hr
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H) tR :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso
        I I (eR ≪≫ R) (eL ≪≫ L ≪≫ H) tR

/-- The two local universal zero ideals have identical pullbacks to every
pairwise overlap of the refined affine product cover. -/
theorem projectiveSectionLocalZeroIdeal_comap_overlap_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroIdeal base M ij).comap
        (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) =
      (C.projectiveSectionLocalZeroIdeal base M kl).comap
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) :=
  (C.projectiveSectionLocalZeroIdeal_comap_overlap_left base M ij kl).trans
    (C.projectiveSectionLocalZeroIdeal_comap_overlap_right base M ij kl).symm
-/

/-- The zero ideal obtained by canonically restricting the left chart
presentation to an overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftRestrictedZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionOpenCoverOverlapLeftRestrictedFreeIso base M ij kl)
    (C.projectiveSectionOpenCoverOverlapLeftRestrictedSection base M ij kl)

/-- The left overlap ideal after restriction-to-pullback and pullback
composition, before congruence of the two surface maps. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionOpenCoverOverlapLeftPreCongrFreeIso base M ij kl)
    (C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection base M ij kl)

/-- The left overlap ideal after congruence of the two surface maps. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionOpenCoverOverlapLeftCommonFreeIso base M ij kl)
    (C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionLocalZeroIdeal_comap_eq_leftRestricted
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroIdeal base M ij).comap
        (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) =
      C.projectiveSectionOpenCoverOverlapLeftRestrictedZeroIdeal base M ij kl := by
  let pL := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  letI : IsAffine ((C.projectiveSectionOpenCover base M).X ij) :=
    C.projectiveSectionOpenCover_affine base M ij
  unfold projectiveSectionLocalZeroIdeal
    projectiveSectionOpenCoverOverlapLeftRestrictedZeroIdeal
  change (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionLocalFreeIso base M ij)
    (C.projectiveSectionLocalUniversalSection base M ij)).comap pL = _
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction
    pL I (C.projectiveSectionLocalFreeIso base M ij)
      (C.projectiveSectionLocalUniversalSection base M ij)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlapLeftRestrictedZeroIdeal_eq_preCongr
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftRestrictedZeroIdeal base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal base M ij kl := by
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  let e := C.projectiveSectionOpenCoverOverlapLeftRestrictedFreeIso base M ij kl
  let sL := C.projectiveSectionOpenCoverOverlapLeftRestrictedSection base M ij kl
  let L := C.projectiveSectionOpenCoverOverlapLeftPreCongrModuleIso base M ij kl
  let tL₀ := C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
    base M ij kl
  dsimp only [projectiveSectionOpenCoverOverlapLeftRestrictedZeroIdeal,
    projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal,
    projectiveSectionOpenCoverOverlapLeftPreCongrFreeIso]
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I e sL =
        BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (e ≪≫ L)
          (SheafOfModules.sectionsMap L.hom sL) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq I e L sL
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (e ≪≫ L) tL₀ := by
      have hp := C.projectiveSectionOpenCoverOverlap_left_preCongr_transport
        base M ij kl
      unfold projectiveSectionOpenCoverOverlapLeftPreCongrSection at hp
      exact congrArg
        (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (e ≪≫ L)) hp

/-
set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal_eq_congruent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal base M ij kl := by
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  let e := C.projectiveSectionOpenCoverOverlapLeftPreCongrFreeIso base M ij kl
  let H := C.projectiveSectionOpenCoverOverlapPullbackCongrModuleIso base M ij kl
  let tL₀ := C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
    base M ij kl
  let tL := C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl
  unfold projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal
    projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L) tL₀ =
        BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H)
          (SheafOfModules.sectionsMap H.hom tL₀) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
        I (eL ≪≫ L) H tL₀
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H) tL := by
      have hc := C.projectiveSectionOpenCoverOverlap_left_universal_congr
        base M ij kl
      unfold projectiveSectionOpenCoverOverlapLeftCongruentSection at hc
      exact congrArg
        (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eL ≪≫ L ≪≫ H)) hc
-/

/-- The pre-congruence ideal after postcomposing its free presentation with
the pullback-congruence isomorphism. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftPostCongrZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  let e := C.projectiveSectionOpenCoverOverlapLeftPreCongrFreeIso base M ij kl
  let H := C.projectiveSectionOpenCoverOverlapPullbackCongrModuleIso base M ij kl
  let tL₀ := C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
    base M ij kl
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (e ≪≫ H)
    (SheafOfModules.sectionsMap H.hom tL₀)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal_eq_postCongr
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftPostCongrZeroIdeal base M ij kl := by
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  let e := C.projectiveSectionOpenCoverOverlapLeftPreCongrFreeIso base M ij kl
  let H := C.projectiveSectionOpenCoverOverlapPullbackCongrModuleIso base M ij kl
  let tL₀ := C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
    base M ij kl
  dsimp only [projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal,
    projectiveSectionOpenCoverOverlapLeftPostCongrZeroIdeal]
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
    I e H tL₀

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlapLeftPostCongrZeroIdeal_eq_congruent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftPostCongrZeroIdeal base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal base M ij kl := by
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  let e := C.projectiveSectionOpenCoverOverlapLeftCommonFreeIso base M ij kl
  dsimp only [projectiveSectionOpenCoverOverlapLeftPostCongrZeroIdeal,
    projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal,
    projectiveSectionOpenCoverOverlapLeftCommonFreeIso]
  have hc := C.projectiveSectionOpenCoverOverlap_left_universal_congr
    base M ij kl
  unfold projectiveSectionOpenCoverOverlapLeftCongruentSection at hc
  exact congrArg
    (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I e) hc

theorem projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal_eq_congruent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal base M ij kl :=
  (C.projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal_eq_postCongr
    base M ij kl).trans
    (C.projectiveSectionOpenCoverOverlapLeftPostCongrZeroIdeal_eq_congruent
      base M ij kl)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal_eq_common
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal base M ij kl =
      C.projectiveSectionOpenCoverOverlapCommonZeroIdeal base M ij kl := by
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  let e := C.projectiveSectionOpenCoverOverlapLeftCommonFreeIso base M ij kl
  let tL := C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl
  let tR := C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl
  let a := BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (C.projectiveSectionOpenCoverOverlapUnit base M ij kl)
  letI : IsIso a :=
    C.isIso_projectiveSectionOpenCoverOverlapUnitCoefficient base M ij kl
  dsimp only [projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal,
    projectiveSectionOpenCoverOverlapCommonZeroIdeal]
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I e tL =
        BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I e
          (BundleSectionZeroLocus.scaleSection a tR) := by
      rw [C.projectiveSectionOpenCoverOverlap_universalSection_commonScale
        base M ij kl]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I e tR :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso
        I e a tR

/-- The left local ideal restricts to the common overlap ideal. -/
theorem projectiveSectionLocalZeroIdeal_comap_overlap_left
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroIdeal base M ij).comap
        (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) =
      C.projectiveSectionOpenCoverOverlapCommonZeroIdeal base M ij kl :=
  (C.projectiveSectionLocalZeroIdeal_comap_eq_leftRestricted base M ij kl).trans
    ((C.projectiveSectionOpenCoverOverlapLeftRestrictedZeroIdeal_eq_preCongr
      base M ij kl).trans
    ((C.projectiveSectionOpenCoverOverlapLeftPreCongrZeroIdeal_eq_congruent
      base M ij kl).trans
      (C.projectiveSectionOpenCoverOverlapLeftCongruentZeroIdeal_eq_common
        base M ij kl)))

/-- The zero ideal obtained by canonically restricting the right chart
presentation to an overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapRightRestrictedZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionOpenCoverOverlapRightRestrictedFreeIso base M ij kl)
    (C.projectiveSectionOpenCoverOverlapRightRestrictedSection base M ij kl)

/-- The right overlap ideal in the common pullback presentation. -/
noncomputable def projectiveSectionOpenCoverOverlapRightCommonZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionOpenCoverOverlapRightCommonFreeIso base M ij kl)
    (C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionLocalZeroIdeal_comap_eq_rightRestricted
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroIdeal base M kl).comap
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) =
      C.projectiveSectionOpenCoverOverlapRightRestrictedZeroIdeal base M ij kl := by
  let pR := pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  letI : IsAffine ((C.projectiveSectionOpenCover base M).X kl) :=
    C.projectiveSectionOpenCover_affine base M kl
  unfold projectiveSectionLocalZeroIdeal
    projectiveSectionOpenCoverOverlapRightRestrictedZeroIdeal
  change (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionLocalFreeIso base M kl)
    (C.projectiveSectionLocalUniversalSection base M kl)).comap pR = _
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction
    pR I (C.projectiveSectionLocalFreeIso base M kl)
      (C.projectiveSectionLocalUniversalSection base M kl)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlapRightRestrictedZeroIdeal_eq_commonPresentation
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapRightRestrictedZeroIdeal base M ij kl =
      C.projectiveSectionOpenCoverOverlapRightCommonZeroIdeal base M ij kl := by
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  let e := C.projectiveSectionOpenCoverOverlapRightRestrictedFreeIso base M ij kl
  let R := C.projectiveSectionOpenCoverOverlapRightToCommonModuleIso base M ij kl
  let sR := C.projectiveSectionOpenCoverOverlapRightRestrictedSection base M ij kl
  let tR := C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl
  dsimp only [projectiveSectionOpenCoverOverlapRightRestrictedZeroIdeal,
    projectiveSectionOpenCoverOverlapRightCommonZeroIdeal,
    projectiveSectionOpenCoverOverlapRightCommonFreeIso]
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I e sR =
        BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (e ≪≫ R)
          (SheafOfModules.sectionsMap R.hom sR) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq I e R sR
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (e ≪≫ R) tR := by
      have hr := C.projectiveSectionOpenCoverOverlap_right_section_transport
        base M ij kl
      unfold projectiveSectionOpenCoverOverlapRightTransportedSection at hr
      exact congrArg
        (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (e ≪≫ R)) hr

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlapRightCommonZeroIdeal_eq_common
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapRightCommonZeroIdeal base M ij kl =
      C.projectiveSectionOpenCoverOverlapCommonZeroIdeal base M ij kl := by
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  let eR := C.projectiveSectionOpenCoverOverlapRightCommonFreeIso base M ij kl
  let eL := C.projectiveSectionOpenCoverOverlapLeftCommonFreeIso base M ij kl
  let tR := C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl
  dsimp only [projectiveSectionOpenCoverOverlapRightCommonZeroIdeal,
    projectiveSectionOpenCoverOverlapCommonZeroIdeal]
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso
    I I eR eL tR

/-- The right local ideal restricts to the common overlap ideal. -/
theorem projectiveSectionLocalZeroIdeal_comap_overlap_right
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroIdeal base M kl).comap
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) =
      C.projectiveSectionOpenCoverOverlapCommonZeroIdeal base M ij kl :=
  (C.projectiveSectionLocalZeroIdeal_comap_eq_rightRestricted base M ij kl).trans
    ((C.projectiveSectionOpenCoverOverlapRightRestrictedZeroIdeal_eq_commonPresentation
      base M ij kl).trans
      (C.projectiveSectionOpenCoverOverlapRightCommonZeroIdeal_eq_common
        base M ij kl))

/-- The two local universal zero ideals have identical pullbacks to every
pairwise overlap of the refined affine product cover. -/
theorem projectiveSectionLocalZeroIdeal_comap_overlap_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroIdeal base M ij).comap
        (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) =
      (C.projectiveSectionLocalZeroIdeal base M kl).comap
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl)) :=
  (C.projectiveSectionLocalZeroIdeal_comap_overlap_left base M ij kl).trans
    (C.projectiveSectionLocalZeroIdeal_comap_overlap_right base M ij kl).symm

end SchemeModuleFiniteFreeAffineCover

end

end PfaffianDescent
