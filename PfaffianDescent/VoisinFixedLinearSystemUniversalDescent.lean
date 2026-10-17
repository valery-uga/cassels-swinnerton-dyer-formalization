import PfaffianDescent.VoisinFixedLinearSystemUniversalFamily

/-!
# Descent of the projective universal section

This file transports the chartwise universal sections to arbitrary overlaps
of the finite affine product cover and identifies their zero ideals.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchemeModuleFiniteFreeAffineCover

/-
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

/-- A single common coordinate ideal on a refined overlap, using the left
restricted free presentation and the right-normalized common equation. -/
noncomputable def projectiveSectionOpenCoverOverlapCommonZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  let pL := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let H := (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)).app M
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (BundleSectionZeroLocus.restrictionFreeIsoOf pL I
        (C.projectiveSectionLocalFreeIso base M ij) ≪≫
      C.projectiveSectionOpenCoverOverlapLeftPreCongrModuleIso base M ij kl ≪≫ H)
    (C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl)

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
/-
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SchemeModuleFiniteFreeAffineCover
-/

/-- The right local universal section restricted to a refined overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapRightRestrictedSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.restrictModuleSection
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))
    (C.projectiveSectionLocalModule base M kl)
    (C.projectiveSectionLocalUniversalSection base M kl)

/-- The restricted right equation transported to the common overlap-module
presentation. -/
noncomputable def projectiveSectionOpenCoverOverlapRightTransportedSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  SheafOfModules.sectionsMap
    (C.projectiveSectionOpenCoverOverlapRightToCommonModuleIso base M ij kl).hom
    (C.projectiveSectionOpenCoverOverlapRightRestrictedSection base M ij kl)

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the right local universal section to an arbitrary refined
overlap gives the right-normalized common equation. -/
theorem projectiveSectionOpenCoverOverlap_right_section_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapRightTransportedSection base M ij kl =
      C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl := by
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  let p := pullback.snd ((C.projectiveSectionOpenCover base M).f (i, j))
    ((C.projectiveSectionOpenCover base M).f (k, l))
  let q := C.projectiveSectionOpenCoverToSurface base M (k, l)
  let A := (Scheme.Modules.restrictFunctorIsoPullback p).app
    (C.projectiveSectionLocalModule base M (k, l))
  let B := (Scheme.Modules.pullbackComp p q).app M
  let s := C.projectiveSectionLocalUniversalSection base M (k, l)
  let sC := C.projectiveSectionOpenCoverOverlapRightRestrictedSection base M (i, j) (k, l)
  change SheafOfModules.sectionsMap (A.hom ≫ B.hom) sC = _
  rw [SheafOfModules.sectionsMap_comp]
  calc
    SheafOfModules.sectionsMap B.hom (SheafOfModules.sectionsMap A.hom sC) =
        SheafOfModules.sectionsMap B.hom
          (BundleSectionZeroLocus.pullbackSection p
            (C.projectiveSectionLocalModule base M (k, l))
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s) := by
      exact congrArg (SheafOfModules.sectionsMap B.hom)
        (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s)
    _ = C.projectiveSectionOpenCoverOverlapRightUniversalSection base M (i, j) (k, l) := by
      unfold projectiveSectionOpenCoverOverlapRightUniversalSection
      dsimp only [s]
      unfold projectiveSectionLocalUniversalSection
      have h := parameterizedSchemeModuleSection_pullback
        (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
        base M q p
        (fun x : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)) =>
          C.projectiveSectionLocalCoefficient base M (k, l) x)
        (fun x : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)) =>
          Module.finBasis K (SchemeModuleGlobalSectionsOver base M) x)
      have hc : (fun x => p.appTop
          (C.projectiveSectionLocalCoefficient base M (k, l) x)) =
          C.projectiveSectionOpenCoverOverlapRightCoefficient base M (i, j) (k, l) := by
        rfl
      rw [hc] at h
      exact h

/-- The left local universal section restricted to a refined overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftRestrictedSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  BundleSectionZeroLocus.restrictModuleSection
    (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))
    (C.projectiveSectionLocalModule base M ij)
    (C.projectiveSectionLocalUniversalSection base M ij)

/-- The restricted left equation transported to the common overlap-module
presentation. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftTransportedSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  SheafOfModules.sectionsMap
    (C.projectiveSectionOpenCoverOverlapLeftToCommonModuleIso base M ij kl).hom
    (C.projectiveSectionOpenCoverOverlapLeftRestrictedSection base M ij kl)

/-
set_option backward.isDefEq.respectTransparency false in
/-- Pulling the left local universal section to an arbitrary refined overlap
and identifying the two surface pullbacks gives the left-normalized common
equation. -/
theorem projectiveSectionOpenCoverOverlap_left_section_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftTransportedSection base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl := by
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  let p := pullback.fst ((C.projectiveSectionOpenCover base M).f (i, j))
    ((C.projectiveSectionOpenCover base M).f (k, l))
  let q := C.projectiveSectionOpenCoverToSurface base M (i, j)
  let r := pullback.snd ((C.projectiveSectionOpenCover base M).f (i, j))
      ((C.projectiveSectionOpenCover base M).f (k, l)) ≫
    C.projectiveSectionOpenCoverToSurface base M (k, l)
  let h := C.projectiveSectionOpenCoverOverlap_toSurface_eq base M (i, j) (k, l)
  let A := (Scheme.Modules.restrictFunctorIsoPullback p).app
    (C.projectiveSectionLocalModule base M (i, j))
  let B := (Scheme.Modules.pullbackComp p q).app M
  let H := (Scheme.Modules.pullbackCongr h).app M
  let s := C.projectiveSectionLocalUniversalSection base M (i, j)
  let sC := C.projectiveSectionOpenCoverOverlapLeftRestrictedSection
    base M (i, j) (k, l)
  change SheafOfModules.sectionsMap (A.hom ≫ B.hom ≫ H.hom) sC = _
  rw [SheafOfModules.sectionsMap_comp, SheafOfModules.sectionsMap_comp]
  calc
    SheafOfModules.sectionsMap H.hom
        (SheafOfModules.sectionsMap B.hom (SheafOfModules.sectionsMap A.hom sC)) =
      SheafOfModules.sectionsMap H.hom
        (SheafOfModules.sectionsMap B.hom
          (BundleSectionZeroLocus.pullbackSection p
            (C.projectiveSectionLocalModule base M (i, j))
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s)) := by
      exact congrArg
        (fun z => SheafOfModules.sectionsMap H.hom
          (SheafOfModules.sectionsMap B.hom z))
        (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s)
    _ = SheafOfModules.sectionsMap H.hom
        (parameterizedSchemeModuleSection base M (p ≫ q)
          (C.projectiveSectionOpenCoverOverlapLeftCoefficient
            base M (i, j) (k, l))
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))) := by
      apply congrArg (SheafOfModules.sectionsMap H.hom)
      dsimp only [s]
      unfold projectiveSectionLocalUniversalSection
      have hb := parameterizedSchemeModuleSection_pullback
        (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
        base M q p
        (fun x => C.projectiveSectionLocalCoefficient base M (i, j) x)
        (fun x => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) x)
      have hc : (fun x => p.appTop
          (C.projectiveSectionLocalCoefficient base M (i, j) x)) =
          C.projectiveSectionOpenCoverOverlapLeftCoefficient
            base M (i, j) (k, l) := by
        rfl
      rw [hc] at hb
      exact hb
    _ = C.projectiveSectionOpenCoverOverlapLeftUniversalSection
        base M (i, j) (k, l) := by
      unfold projectiveSectionOpenCoverOverlapLeftUniversalSection
      exact parameterizedSchemeModuleSection_pullbackCongr
        (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
        base M (p ≫ q) r h
        (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M (i, j) (k, l))
        (fun x => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) x)
-/

/-- The restricted left equation transported through restriction and
pullback composition, before identifying the equal surface composites. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftPreCongrSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  let p := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let q := C.projectiveSectionOpenCoverToSurface base M ij
  SheafOfModules.sectionsMap
    (((Scheme.Modules.restrictFunctorIsoPullback p).app
      (C.projectiveSectionLocalModule base M ij) ≪≫
      (Scheme.Modules.pullbackComp p q).app M).hom)
    (C.projectiveSectionOpenCoverOverlapLeftRestrictedSection base M ij kl)

/-- The corresponding parameterized equation before transport along the
equality of surface composites. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  parameterizedSchemeModuleSection base M
    (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl) ≫
      C.projectiveSectionOpenCoverToSurface base M ij)
    (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M ij kl)
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlap_left_preCongr_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftPreCongrSection base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
        base M ij kl := by
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  let p := pullback.fst ((C.projectiveSectionOpenCover base M).f (i, j))
    ((C.projectiveSectionOpenCover base M).f (k, l))
  let q := C.projectiveSectionOpenCoverToSurface base M (i, j)
  let A := (Scheme.Modules.restrictFunctorIsoPullback p).app
    (C.projectiveSectionLocalModule base M (i, j))
  let B := (Scheme.Modules.pullbackComp p q).app M
  let s := C.projectiveSectionLocalUniversalSection base M (i, j)
  let sC := C.projectiveSectionOpenCoverOverlapLeftRestrictedSection
    base M (i, j) (k, l)
  change SheafOfModules.sectionsMap (A.hom ≫ B.hom) sC = _
  rw [SheafOfModules.sectionsMap_comp]
  calc
    SheafOfModules.sectionsMap B.hom (SheafOfModules.sectionsMap A.hom sC) =
        SheafOfModules.sectionsMap B.hom
          (BundleSectionZeroLocus.pullbackSection p
            (C.projectiveSectionLocalModule base M (i, j))
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s) := by
      exact congrArg (SheafOfModules.sectionsMap B.hom)
        (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s)
    _ = C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
        base M (i, j) (k, l) := by
      unfold projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
      dsimp only [s]
      unfold projectiveSectionLocalUniversalSection
      have h := parameterizedSchemeModuleSection_pullback
        (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
        base M q p
        (fun x => C.projectiveSectionLocalCoefficient base M (i, j) x)
        (fun x => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) x)
      have hc : (fun x => p.appTop
          (C.projectiveSectionLocalCoefficient base M (i, j) x)) =
          C.projectiveSectionOpenCoverOverlapLeftCoefficient
            base M (i, j) (k, l) := by
        rfl
      rw [hc] at h
      exact h

/-
set_option backward.isDefEq.respectTransparency false in
/-- Full transport of the restricted left equation to the common right-hand
pullback presentation. -/
theorem projectiveSectionOpenCoverOverlap_left_section_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftTransportedSection base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl := by
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  let h := C.projectiveSectionOpenCoverOverlap_toSurface_eq base M (i, j) (k, l)
  let H := (Scheme.Modules.pullbackCongr h).app M
  change SheafOfModules.sectionsMap H.hom
    (C.projectiveSectionOpenCoverOverlapLeftPreCongrSection
      base M (i, j) (k, l)) = _
  rw [C.projectiveSectionOpenCoverOverlap_left_preCongr_transport
    base M (i, j) (k, l)]
  unfold projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
    projectiveSectionOpenCoverOverlapLeftUniversalSection
  exact parameterizedSchemeModuleSection_pullbackCongr
    (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    base M _ _ h
    (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M (i, j) (k, l))
    (fun x => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) x)
-/

/-- The pre-congruence left equation transported along equality of the two
surface composites. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftCongruentSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  SheafOfModules.sectionsMap
    ((Scheme.Modules.pullbackCongr
      (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)).app M).hom
    (C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection base M ij kl)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlap_left_universal_congr
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftCongruentSection base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl := by
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  unfold projectiveSectionOpenCoverOverlapLeftCongruentSection
    projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
    projectiveSectionOpenCoverOverlapLeftUniversalSection
  exact parameterizedSchemeModuleSection_pullbackCongr
    (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    base M _ _
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M (i, j) (k, l))
    (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M (i, j) (k, l))
    (fun x => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) x)

/-
set_option backward.isDefEq.respectTransparency false in
/-- Full transport of the restricted left equation to the common right-hand
pullback presentation. -/
theorem projectiveSectionOpenCoverOverlap_left_section_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftTransportedSection base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl := by
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  let H := (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M (i, j) (k, l))).app M
  change SheafOfModules.sectionsMap H.hom
    (C.projectiveSectionOpenCoverOverlapLeftPreCongrSection
      base M (i, j) (k, l)) = _
  calc
    _ = SheafOfModules.sectionsMap H.hom
        (C.projectiveSectionOpenCoverOverlapLeftPreCongrUniversalSection
          base M (i, j) (k, l)) := by
      exact congrArg (SheafOfModules.sectionsMap H.hom)
        (C.projectiveSectionOpenCoverOverlap_left_preCongr_transport
          base M (i, j) (k, l))
    _ = _ := C.projectiveSectionOpenCoverOverlap_left_universal_congr
      base M (i, j) (k, l)
-/

/-
set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlap_left_transport_to_congruent
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftTransportedSection base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftCongruentSection base M ij kl := by
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  let p := pullback.fst ((C.projectiveSectionOpenCover base M).f (i, j))
    ((C.projectiveSectionOpenCover base M).f (k, l))
  let q := C.projectiveSectionOpenCoverToSurface base M (i, j)
  let A := (Scheme.Modules.restrictFunctorIsoPullback p).app
    (C.projectiveSectionLocalModule base M (i, j))
  let B := (Scheme.Modules.pullbackComp p q).app M
  let H := (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M (i, j) (k, l))).app M
  have he : (C.projectiveSectionOpenCoverOverlapLeftToCommonModuleIso
      base M (i, j) (k, l)).hom = (A ≪≫ B).hom ≫ H.hom := by rfl
  unfold projectiveSectionOpenCoverOverlapLeftTransportedSection
    projectiveSectionOpenCoverOverlapLeftCongruentSection
  rw [he, SheafOfModules.sectionsMap_comp]
  change SheafOfModules.sectionsMap H.hom
    (C.projectiveSectionOpenCoverOverlapLeftPreCongrSection
      base M (i, j) (k, l)) = _
  rw [C.projectiveSectionOpenCoverOverlap_left_preCongr_transport
    base M (i, j) (k, l)]

/-- Full transport of the restricted left equation to the common right-hand
pullback presentation. -/
theorem projectiveSectionOpenCoverOverlap_left_section_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapLeftTransportedSection base M ij kl =
      C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl :=
  (C.projectiveSectionOpenCoverOverlap_left_transport_to_congruent
    base M ij kl).trans
  (C.projectiveSectionOpenCoverOverlap_left_universal_congr base M ij kl)
-/

/-
set_option backward.isDefEq.respectTransparency false in
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
          ((C.projectiveSectionOpenCover base M).f kl)) := by
  let pL := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let pR := pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  letI : IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) :=
    C.projectiveSectionOpenCoverOverlap_affine base M ij kl
  letI : IsAffine ((C.projectiveSectionOpenCover base M).X ij) :=
    C.projectiveSectionOpenCover_affine base M ij
  letI : IsAffine ((C.projectiveSectionOpenCover base M).X kl) :=
    C.projectiveSectionOpenCover_affine base M kl
  let eL := BundleSectionZeroLocus.restrictionFreeIsoOf pL I
    (C.projectiveSectionLocalFreeIso base M ij)
  let eR := BundleSectionZeroLocus.restrictionFreeIsoOf pR I
    (C.projectiveSectionLocalFreeIso base M kl)
  let sL := C.projectiveSectionOpenCoverOverlapLeftRestrictedSection base M ij kl
  let sR := C.projectiveSectionOpenCoverOverlapRightRestrictedSection base M ij kl
  let qL := C.projectiveSectionOpenCoverToSurface base M ij
  let A := (Scheme.Modules.restrictFunctorIsoPullback pL).app
    (C.projectiveSectionLocalModule base M ij)
  let B := (Scheme.Modules.pullbackComp pL qL).app M
  let L := A ≪≫ B
  let H := (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)).app M
  let R := C.projectiveSectionOpenCoverOverlapRightToCommonModuleIso base M ij kl
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
      (C.projectiveSectionLocalUniversalSection base M ij)).comap pL =
    (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
      (C.projectiveSectionLocalFreeIso base M kl)
      (C.projectiveSectionLocalUniversalSection base M kl)).comap pR
  rw [BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction
      pL I (C.projectiveSectionLocalFreeIso base M ij)
        (C.projectiveSectionLocalUniversalSection base M ij),
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction
      pR I (C.projectiveSectionLocalFreeIso base M kl)
        (C.projectiveSectionLocalUniversalSection base M kl)]
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
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eR ≪≫ R) tR :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso
        I I (eL ≪≫ L ≪≫ H) (eR ≪≫ R) tR
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eR ≪≫ R)
          (SheafOfModules.sectionsMap R.hom sR) := by
      have hr := C.projectiveSectionOpenCoverOverlap_right_section_transport
        base M ij kl
      unfold projectiveSectionOpenCoverOverlapRightTransportedSection at hr
      exact congrArg
        (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I (eR ≪≫ R)) hr.symm
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I eR sR :=
      (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq I eR R sR).symm
-/

end SchemeModuleFiniteFreeAffineCover

end

end PfaffianDescent
