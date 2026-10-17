import PfaffianDescent.VoisinFixedLinearSystemUniversalZeroIdealDescent

/-!
# Zero-subscheme descent for the projective universal section

The equality of the two pulled-back local zero ideals is promoted to
transition isomorphisms between the corresponding overlap subschemes.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace SchemeModuleFiniteFreeAffineCover

/-- Transport along equality of ideal data commutes with the corresponding
closed immersions. -/
theorem universalIdealSheafData_eqToIso_subschemeι
    {Y : Scheme.{u}} (J L : Y.IdealSheafData) (h : J = L) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
      L.subschemeι = J.subschemeι := by
  subst L
  simp

/-- The restriction of the left local zero subscheme to a refined overlap. -/
noncomputable abbrev projectiveSectionLocalZeroOverlap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) : Scheme.{u} :=
  ((C.projectiveSectionLocalZeroIdeal base M ij).comap
    (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))).subscheme

/-- The same overlap expressed using the right local zero subscheme. -/
noncomputable abbrev projectiveSectionLocalZeroOverlapRight
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) : Scheme.{u} :=
  ((C.projectiveSectionLocalZeroIdeal base M kl).comap
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))).subscheme

/-- The overlap is open in the left local zero subscheme. -/
noncomputable def projectiveSectionLocalZeroOverlapι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlap base M ij kl ⟶
      C.projectiveSectionLocalZeroSubscheme base M ij :=
  let pL := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  ((C.projectiveSectionLocalZeroIdeal base M ij).comapIso pL).hom ≫
    pullback.snd pL (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι

/-- The right presentation of an overlap is open in the right local zero
subscheme. -/
noncomputable def projectiveSectionLocalZeroOverlapRightι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapRight base M ij kl ⟶
      C.projectiveSectionLocalZeroSubscheme base M kl :=
  let pR := pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  ((C.projectiveSectionLocalZeroIdeal base M kl).comapIso pR).hom ≫
    pullback.snd pR (C.projectiveSectionLocalZeroIdeal base M kl).subschemeι

instance isOpenImmersion_projectiveSectionLocalZeroOverlapι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    IsOpenImmersion (C.projectiveSectionLocalZeroOverlapι base M ij kl) := by
  let pL := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let J := C.projectiveSectionLocalZeroIdeal base M ij
  change IsOpenImmersion ((J.comapIso pL).hom ≫ pullback.snd pL J.subschemeι)
  letI : IsOpenImmersion pL :=
    C.isOpenImmersion_projectiveSectionOpenCoverOverlap_fst base M ij kl
  letI : IsOpenImmersion (pullback.snd pL J.subschemeι) := inferInstance
  infer_instance

instance isOpenImmersion_projectiveSectionLocalZeroOverlapRightι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    IsOpenImmersion (C.projectiveSectionLocalZeroOverlapRightι base M ij kl) := by
  let pR := pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let J := C.projectiveSectionLocalZeroIdeal base M kl
  change IsOpenImmersion ((J.comapIso pR).hom ≫ pullback.snd pR J.subschemeι)
  letI : IsOpenImmersion pR :=
    C.isOpenImmersion_projectiveSectionOpenCoverOverlap_snd base M ij kl
  letI : IsOpenImmersion (pullback.snd pR J.subschemeι) := inferInstance
  infer_instance

/-- Equality of the pulled-back ideals induces the transition between the
left and right presentations of a refined overlap. -/
noncomputable def projectiveSectionLocalZeroOverlapIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlap base M ij kl ≅
      C.projectiveSectionLocalZeroOverlapRight base M ij kl :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (C.projectiveSectionLocalZeroIdeal_comap_overlap_eq base M ij kl))

/-- Reindex the right presentation along symmetry of the ambient pullback. -/
noncomputable def projectiveSectionLocalZeroOverlapReindexIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapRight base M ij kl ≅
      C.projectiveSectionLocalZeroOverlap base M kl ij := by
  let f := (C.projectiveSectionOpenCover base M).f ij
  let g := (C.projectiveSectionOpenCover base M).f kl
  let r := (pullbackSymmetry f g).hom
  let J := C.projectiveSectionLocalZeroIdeal base M kl
  let pR := pullback.snd f g
  let pL := pullback.fst g f
  have hcomp : r ≫ pL = pR := pullbackSymmetry_hom_comp_fst f g
  have hcomap : J.comap pR = (J.comap pL).comap r := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  exact eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap) ≪≫
    (J.comap pL).comapIso r ≪≫ asIso (pullback.snd r (J.comap pL).subschemeι)

/-- Reindexing the right overlap presentation preserves its canonical map
to the right local zero subscheme. -/
theorem projectiveSectionLocalZeroOverlapReindexIso_hom_comp_ι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroOverlapReindexIso base M ij kl).hom ≫
        C.projectiveSectionLocalZeroOverlapι base M kl ij =
      C.projectiveSectionLocalZeroOverlapRightι base M ij kl := by
  let f := (C.projectiveSectionOpenCover base M).f ij
  let g := (C.projectiveSectionOpenCover base M).f kl
  let r := (pullbackSymmetry f g).hom
  let J := C.projectiveSectionLocalZeroIdeal base M kl
  let pR := pullback.snd f g
  let pL := pullback.fst g f
  have hcomp : r ≫ pL = pR := pullbackSymmetry_hom_comp_fst f g
  have hcomap : J.comap pR = (J.comap pL).comap r := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  change (eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap) ≪≫
      (J.comap pL).comapIso r ≪≫
        asIso (pullback.snd r (J.comap pL).subschemeι)).hom ≫
      (J.comapIso pL).hom ≫ pullback.snd pL J.subschemeι =
    (J.comapIso pR).hom ≫ pullback.snd pR J.subschemeι
  apply (cancel_mono J.subschemeι).mp
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition (f := pL) (g := J.subschemeι)]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← pullback.condition_assoc (f := r)
    (g := (J.comap pL).subschemeι) (h := pL)]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← Category.assoc]
  rw [universalIdealSheafData_eqToIso_subschemeι]
  · rw [hcomp]
    rw [← pullback.condition (f := pR) (g := J.subschemeι)]
    rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  · exact hcomap

/-- The canonical transition between oppositely ordered local overlaps. -/
noncomputable def projectiveSectionLocalZeroOverlapSwap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlap base M ij kl ≅
      C.projectiveSectionLocalZeroOverlap base M kl ij :=
  C.projectiveSectionLocalZeroOverlapIso base M ij kl ≪≫
    C.projectiveSectionLocalZeroOverlapReindexIso base M ij kl

/-- The map from a left overlap presentation to the right local zero
subscheme. -/
noncomputable def projectiveSectionLocalZeroOverlapRightMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlap base M ij kl ⟶
      C.projectiveSectionLocalZeroSubscheme base M kl :=
  (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom ≫
    C.projectiveSectionLocalZeroOverlapι base M kl ij

theorem projectiveSectionLocalZeroOverlapSwap_hom_comp_left_eq_rightMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom ≫
      C.projectiveSectionLocalZeroOverlapι base M kl ij =
        C.projectiveSectionLocalZeroOverlapRightMap base M ij kl := rfl

/-- The direct left-to-right ideal transition followed by the right overlap
map equals the transition map used for gluing. -/
@[reassoc]
theorem projectiveSectionLocalZeroOverlapIso_hom_comp_rightι_eq_rightMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroOverlapIso base M ij kl).hom ≫
        C.projectiveSectionLocalZeroOverlapRightι base M ij kl =
      C.projectiveSectionLocalZeroOverlapRightMap base M ij kl := by
  unfold projectiveSectionLocalZeroOverlapRightMap
    projectiveSectionLocalZeroOverlapSwap
  simp only [Iso.trans_hom, Category.assoc]
  rw [C.projectiveSectionLocalZeroOverlapReindexIso_hom_comp_ι base M ij kl]

instance mono_projectiveSectionLocalZeroOverlapι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    Mono (C.projectiveSectionLocalZeroOverlapι base M ij kl) :=
  (C.isOpenImmersion_projectiveSectionLocalZeroOverlapι base M ij kl).mono

/-- The left overlap inclusion followed by the local closed immersion is
the canonical closed subscheme of the ambient overlap. -/
theorem projectiveSectionLocalZeroOverlapι_comp_subschemeι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapι base M ij kl ≫
        (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι =
      ((C.projectiveSectionLocalZeroIdeal base M ij).comap
        (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl))).subschemeι ≫
        pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl) := by
  unfold projectiveSectionLocalZeroOverlapι projectiveSectionLocalZeroOverlap
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- Restricting a local zero subscheme to an ambient chart overlap is a
pullback square. -/
theorem isPullback_projectiveSectionLocalZeroOverlap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    IsPullback
      ((C.projectiveSectionLocalZeroIdeal base M ij).comap
        (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl))).subschemeι
      (C.projectiveSectionLocalZeroOverlapι base M ij kl)
      (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl))
      (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι := by
  apply AlgebraicGeometry.isPullback_of_isClosedImmersion
  · exact (C.projectiveSectionLocalZeroOverlapι_comp_subschemeι
      base M ij kl).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]

/-- The analogous ambient factorization for the right overlap presentation. -/
theorem projectiveSectionLocalZeroOverlapRightι_comp_subschemeι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapRightι base M ij kl ≫
        (C.projectiveSectionLocalZeroIdeal base M kl).subschemeι =
      ((C.projectiveSectionLocalZeroIdeal base M kl).comap
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl))).subschemeι ≫
        pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl) := by
  unfold projectiveSectionLocalZeroOverlapRightι projectiveSectionLocalZeroOverlapRight
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- The right overlap map has its explicit factorization through the right
pulled-back zero ideal. -/
@[reassoc]
theorem projectiveSectionLocalZeroOverlapRightMap_comp_subschemeι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapRightMap base M ij kl ≫
        (C.projectiveSectionLocalZeroIdeal base M kl).subschemeι =
      (C.projectiveSectionLocalZeroOverlapIso base M ij kl).hom ≫
        ((C.projectiveSectionLocalZeroIdeal base M kl).comap
          (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
            ((C.projectiveSectionOpenCover base M).f kl))).subschemeι ≫
          pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
            ((C.projectiveSectionOpenCover base M).f kl) := by
  rw [← C.projectiveSectionLocalZeroOverlapIso_hom_comp_rightι_eq_rightMap
    base M ij kl, Category.assoc,
    C.projectiveSectionLocalZeroOverlapRightι_comp_subschemeι base M ij kl]

/-- The left and right presentations of an overlap induce the same map to
the ambient universal product. -/
@[reassoc]
theorem projectiveSectionLocalZeroOverlapRightMap_comp_ambient_eq_left
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapRightMap base M ij kl ≫
        (C.projectiveSectionLocalZeroIdeal base M kl).subschemeι ≫
        (C.projectiveSectionOpenCover base M).f kl =
      C.projectiveSectionLocalZeroOverlapι base M ij kl ≫
        (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι ≫
        (C.projectiveSectionOpenCover base M).f ij := by
  rw [C.projectiveSectionLocalZeroOverlapRightMap_comp_subschemeι_assoc
    base M ij kl]
  rw [← Category.assoc (C.projectiveSectionLocalZeroOverlapι base M ij kl)]
  rw [C.projectiveSectionLocalZeroOverlapι_comp_subschemeι base M ij kl]
  unfold projectiveSectionLocalZeroOverlapIso
  rw [← Category.assoc (eqToIso _).hom]
  rw [universalIdealSheafData_eqToIso_subschemeι]
  · simp only [Category.assoc]
    rw [pullback.condition
      (f := (C.projectiveSectionOpenCover base M).f ij)
      (g := (C.projectiveSectionOpenCover base M).f kl)]
  · exact C.projectiveSectionLocalZeroIdeal_comap_overlap_eq base M ij kl

/-- Swapping an overlap and then taking the right local map in the reversed
order recovers the original left restriction. -/
theorem projectiveSectionLocalZeroOverlapSwap_hom_comp_rightMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M kl ij =
      C.projectiveSectionLocalZeroOverlapι base M ij kl := by
  apply (cancel_mono
    (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι).mp
  apply (cancel_mono ((C.projectiveSectionOpenCover base M).f ij)).mp
  simp only [Category.assoc]
  calc
    (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom ≫
        C.projectiveSectionLocalZeroOverlapRightMap base M kl ij ≫
        (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι ≫
        (C.projectiveSectionOpenCover base M).f ij =
      (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom ≫
        C.projectiveSectionLocalZeroOverlapι base M kl ij ≫
        (C.projectiveSectionLocalZeroIdeal base M kl).subschemeι ≫
        (C.projectiveSectionOpenCover base M).f kl := by
          rw [C.projectiveSectionLocalZeroOverlapRightMap_comp_ambient_eq_left
            base M kl ij]
    _ = C.projectiveSectionLocalZeroOverlapRightMap base M ij kl ≫
        (C.projectiveSectionLocalZeroIdeal base M kl).subschemeι ≫
        (C.projectiveSectionOpenCover base M).f kl := by
          rw [← Category.assoc
            (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom]
          rw [C.projectiveSectionLocalZeroOverlapSwap_hom_comp_left_eq_rightMap
            base M ij kl]
    _ = C.projectiveSectionLocalZeroOverlapι base M ij kl ≫
        (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι ≫
        (C.projectiveSectionOpenCover base M).f ij := by
          rw [C.projectiveSectionLocalZeroOverlapRightMap_comp_ambient_eq_left
            base M ij kl]

/-- Oppositely ordered pairwise transition maps are mutually inverse. -/
theorem projectiveSectionLocalZeroOverlapSwap_hom_comp_swap_hom
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroOverlapSwap base M ij kl).hom ≫
        (C.projectiveSectionLocalZeroOverlapSwap base M kl ij).hom = 𝟙 _ := by
  apply (cancel_mono (C.projectiveSectionLocalZeroOverlapι base M ij kl)).mp
  simp only [Category.assoc]
  rw [C.projectiveSectionLocalZeroOverlapSwap_hom_comp_left_eq_rightMap
    base M kl ij]
  rw [C.projectiveSectionLocalZeroOverlapSwap_hom_comp_rightMap base M ij kl]
  simp

/-- On a diagonal overlap the right and left maps coincide. -/
theorem projectiveSectionLocalZeroOverlapRightMap_self
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroOverlapRightMap base M ij ij =
      C.projectiveSectionLocalZeroOverlapι base M ij ij := by
  apply (cancel_mono
    (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι).mp
  apply (cancel_mono ((C.projectiveSectionOpenCover base M).f ij)).mp
  have h := C.projectiveSectionLocalZeroOverlapRightMap_comp_ambient_eq_left
    base M ij ij
  simpa only [Category.assoc] using h

/-- The transition on a diagonal overlap is the identity. -/
theorem projectiveSectionLocalZeroOverlapSwap_self
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalZeroOverlapSwap base M ij ij).hom = 𝟙 _ := by
  apply (cancel_mono (C.projectiveSectionLocalZeroOverlapι base M ij ij)).mp
  rw [C.projectiveSectionLocalZeroOverlapSwap_hom_comp_left_eq_rightMap
    base M ij ij]
  rw [C.projectiveSectionLocalZeroOverlapRightMap_self base M ij]
  simp

end SchemeModuleFiniteFreeAffineCover

end

end PfaffianDescent
