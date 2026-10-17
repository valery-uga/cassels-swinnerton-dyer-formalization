import PfaffianDescent.VoisinFieldBaseChangeOpenCanonicalPullback
import PfaffianDescent.VoisinSchemeModuleCechBaseChange

/-!
# Čech assembly of canonical field base change for module sections

This file instantiates the finite-cover Čech theorem with the canonical local
field-base-change equivalences.  The local maps are independent of the chosen
free presentation and commute with both restriction maps on overlaps.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

/-- Transport a restriction identity across an equality of its target opens.
This isolates the dependent proof transport needed because inverse image
preserves intersections propositionally. -/
theorem schemeModuleOpenSectionsRestriction_eq_cast_of_open_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {A C D : X.Opens} (e : C = A) (hCD : C ≤ D) (hAD : A ≤ D)
    (s : SchemeModuleOpenSectionsOver base M D)
    (t : SchemeModuleOpenSectionsOver base M C)
    (h : schemeModuleOpenSectionsRestrictionLinearMap base M hCD s = t) :
    schemeModuleOpenSectionsRestrictionLinearMap base M hAD s =
      LinearEquiv.cast (R := K)
        (M := fun Z : X.Opens => SchemeModuleOpenSectionsOver base M Z)
        e t := by
  subst A
  rw [Subsingleton.elim hAD hCD]
  exact h

/-- Transport a restriction identity from the inverse image of an intersection
to the intersection of the inverse images. -/
theorem schemeModuleOpenSectionsRestriction_eq_cast_preimage_inf
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (ML : (schemeFieldBaseChange (L := L) base).Modules)
    {U W D : X.Opens} (hCD : U ⊓ W ≤ D)
    (hAD :
      schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U ⊓
          schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ W ≤
        schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ D)
    (s : SchemeModuleOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML
      (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ D))
    (t : SchemeModuleOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML
      (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ (U ⊓ W)))
    (h : schemeModuleOpenSectionsRestrictionLinearMap
      (schemeFieldBaseChangeToField (L := L) base) ML
      ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hCD) s = t) :
    schemeModuleOpenSectionsRestrictionLinearMap
        (schemeFieldBaseChangeToField (L := L) base) ML hAD s =
      LinearEquiv.cast (R := L)
        (M := fun Z : (schemeFieldBaseChange (L := L) base).Opens =>
          SchemeModuleOpenSectionsOver
            (schemeFieldBaseChangeToField (L := L) base) ML Z)
        ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_inf
          (U := U) (V := W)) t := by
  exact schemeModuleOpenSectionsRestriction_eq_cast_of_open_eq
    (schemeFieldBaseChangeToField (L := L) base) ML
    ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_inf
      (U := U) (V := W))
    ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hCD)
    hAD s t h

/-- The canonical local field-base-change equivalence on one affine member of
a cover. -/
noncomputable def schemeFieldBaseChangeCoverLocalEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U : X.Opens) (I : Type u) [Fintype I] [DecidableEq I]
    (tU : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (hU : IsAffine (U : Scheme.{u})) :
    (L ⊗[K] SchemeModuleOpenSectionsOver base M U) ≃ₗ[L]
      SchemeModuleOpenSectionsOver
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
        (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U) := by
  letI : IsAffine (U : Scheme.{u}) := hU
  exact schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv base M U I tU

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical local cover equivalence sends a pure tensor to the scalar
multiple of the intrinsic pullback section. -/
theorem schemeFieldBaseChangeCoverLocalEquiv_tmul_eq_smul_pullback
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U : X.Opens) (I : Type u) [Fintype I] [DecidableEq I]
    (tU : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (hU : IsAffine (U : Scheme.{u}))
    (c : L) (s : SchemeModuleOpenSectionsOver base M U) :
    schemeFieldBaseChangeCoverLocalEquiv base M U I tU hU (c ⊗ₜ[K] s) =
      c • schemeFieldBaseChangeOpenPullbackSection (L := L) base M U s := by
  letI : IsAffine (U : Scheme.{u}) := hU
  exact @schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_eq_smul_pullback
    K L _ _ _ X base M U hU I _ _ tU c s

/-- The canonical overlap equivalence, transported from the inverse image of
the intersection to the intersection of the inverse images. -/
noncomputable def schemeFieldBaseChangeCoverOverlapEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U W : X.Opens) (I : Type u) [Fintype I] [DecidableEq I]
    (tU : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (hUW : IsAffine ((U ⊓ W : X.Opens) : Scheme.{u})) :
    (L ⊗[K] SchemeModuleOpenSectionsOver base M (U ⊓ W)) ≃ₗ[L]
      SchemeModuleOpenSectionsOver
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
        (schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ U ⊓
          schemeFieldBaseChangeToOriginal (L := L) base ⁻¹ᵁ W) := by
  letI : IsAffine ((U ⊓ W : X.Opens) : Scheme.{u}) := hUW
  exact schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
      base M (U ⊓ W) I
        (BundleSectionZeroLocus.restrictFreeIsoOver
          (homOfLE inf_le_left) I tU) ≪≫ₗ
    LinearEquiv.cast (R := L)
      (M := fun Z : (schemeFieldBaseChange (L := L) base).Opens =>
        SchemeModuleOpenSectionsOver
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback
            (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) Z)
      ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_inf
        (U := U) (V := W))

/-- Compatibility of the canonical local equivalence with the left overlap
restriction. -/
theorem schemeFieldBaseChangeCoverLocalEquiv_restrict_left
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U W : X.Opens) (I : Type u) [Fintype I] [DecidableEq I]
    (tU : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (hU : IsAffine (U : Scheme.{u}))
    (hUW : IsAffine ((U ⊓ W : X.Opens) : Scheme.{u}))
    (x : L ⊗[K] SchemeModuleOpenSectionsOver base M U) :
    schemeModuleOpenSectionsRestrictionLinearMap
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
        inf_le_left
        (schemeFieldBaseChangeCoverLocalEquiv base M U I tU hU x) =
      schemeFieldBaseChangeCoverOverlapEquiv base M U W I tU hUW
        (TensorProduct.AlgebraTensorModule.lTensor L L
          (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_left) x) := by
  letI : IsAffine (U : Scheme.{u}) := hU
  letI : IsAffine ((U ⊓ W : X.Opens) : Scheme.{u}) := hUW
  have h := schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_restrict
    (K := K) (L := L) (X := X) (U := U) (W := U ⊓ W)
    base M inf_le_left I tU x
  have ht := schemeModuleOpenSectionsRestriction_eq_cast_preimage_inf
    base ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
    (U := U) (W := W) (D := U) inf_le_left inf_le_left _ _ h
  have hlocal : schemeFieldBaseChangeCoverLocalEquiv base M U I tU hU =
      schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
        (K := K) (L := L) (X := X) base M U I tU := rfl
  have hoverlap : schemeFieldBaseChangeCoverOverlapEquiv
      base M U W I tU hUW =
        schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
            (K := K) (L := L) (X := X) base M (U ⊓ W) I
              (BundleSectionZeroLocus.restrictFreeIsoOver
                (homOfLE inf_le_left) I tU) ≪≫ₗ
          LinearEquiv.cast (R := L)
            (M := fun Z : (schemeFieldBaseChange (L := L) base).Opens =>
              SchemeModuleOpenSectionsOver
                (schemeFieldBaseChangeToField (L := L) base)
                ((Scheme.Modules.pullback
                  (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) Z)
            ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_inf
              (U := U) (V := W)) := rfl
  rw [hlocal, hoverlap]
  exact ht

/-- Compatibility of the canonical local equivalence with the right overlap
restriction; independence of the overlap trivialization supplies the bridge. -/
theorem schemeFieldBaseChangeCoverLocalEquiv_restrict_right
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U W : X.Opens) (I : Type u) [Fintype I] [DecidableEq I]
    (tU : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (tW : SheafOfModules.free (R := X.ringCatSheaf.over W) I ≅ M.over W)
    (hW : IsAffine (W : Scheme.{u}))
    (hUW : IsAffine ((U ⊓ W : X.Opens) : Scheme.{u}))
    (x : L ⊗[K] SchemeModuleOpenSectionsOver base M W) :
    schemeModuleOpenSectionsRestrictionLinearMap
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
        inf_le_right
        (schemeFieldBaseChangeCoverLocalEquiv base M W I tW hW x) =
      schemeFieldBaseChangeCoverOverlapEquiv base M U W I tU hUW
        (TensorProduct.AlgebraTensorModule.lTensor L L
          (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_right) x) := by
  letI : IsAffine (W : Scheme.{u}) := hW
  letI : IsAffine ((U ⊓ W : X.Opens) : Scheme.{u}) := hUW
  have hNat := schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_restrict
    (K := K) (L := L) (X := X) (U := W) (W := U ⊓ W)
    base M inf_le_right I tW x
  have hInd :=
    schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_independent
      (K := K) (L := L) (X := X) base M (U ⊓ W) I I
      (BundleSectionZeroLocus.restrictFreeIsoOver
        (homOfLE inf_le_right) I tW)
      (BundleSectionZeroLocus.restrictFreeIsoOver
        (homOfLE inf_le_left) I tU)
      (TensorProduct.AlgebraTensorModule.lTensor L L
        (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_right) x)
  have hCore := hNat.trans hInd
  have ht := schemeModuleOpenSectionsRestriction_eq_cast_preimage_inf
    base ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
    (U := U) (W := W) (D := W) inf_le_right inf_le_right _ _ hCore
  have hlocal : schemeFieldBaseChangeCoverLocalEquiv base M W I tW hW =
      schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
        (K := K) (L := L) (X := X) base M W I tW := rfl
  have hoverlap : schemeFieldBaseChangeCoverOverlapEquiv
      base M U W I tU hUW =
        schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
            (K := K) (L := L) (X := X) base M (U ⊓ W) I
              (BundleSectionZeroLocus.restrictFreeIsoOver
                (homOfLE inf_le_left) I tU) ≪≫ₗ
          LinearEquiv.cast (R := L)
            (M := fun Z : (schemeFieldBaseChange (L := L) base).Opens =>
              SchemeModuleOpenSectionsOver
                (schemeFieldBaseChangeToField (L := L) base)
                ((Scheme.Modules.pullback
                  (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) Z)
            ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_inf
              (U := U) (V := W)) := rfl
  rw [hlocal, hoverlap]
  exact ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Global module sections commute with field extension when a finite affine
cover trivializes the module and its pairwise intersections are affine. -/
opaque schemeModuleOpenSectionsFieldBaseChangeLinearEquivOfFiniteFreeCover
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → X.Opens) (hcover : ⊤ ≤ ⨆ i, V i)
    (hAffine : ∀ i, IsAffine (V i : Scheme.{u}))
    (hOverlapAffine : ∀ i j, IsAffine ((V i ⊓ V j : X.Opens) : Scheme.{u}))
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : ∀ i,
      SheafOfModules.free (R := X.ringCatSheaf.over (V i)) I ≅
        M.over (V i)) :
    (L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) ≃ₗ[L]
      SchemeModuleOpenSectionsOver
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) ⊤ := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let VL : ι → (schemeFieldBaseChange (L := L) base).Opens :=
    fun i => g ⁻¹ᵁ V i
  have hcoverL : ⊤ ≤ ⨆ i, VL i := by
    have hV : ⨆ i, V i = ⊤ := top_unique hcover
    dsimp only [VL]
    rw [g.iSup_preimage_eq_top hV]
  exact schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents
    base (schemeFieldBaseChangeToField (L := L) base) M
    ((Scheme.Modules.pullback g).obj M) V VL hcover hcoverL
    (fun i => schemeFieldBaseChangeCoverLocalEquiv
      base M (V i) I (t i) (hAffine i))
    (fun i j => schemeFieldBaseChangeCoverOverlapEquiv
      base M (V i) (V j) I (t i) (hOverlapAffine i j))
    (by
      intro i j x
      exact schemeFieldBaseChangeCoverLocalEquiv_restrict_left
        base M (V i) (V j) I (t i) (hAffine i) (hOverlapAffine i j) x)
    (by
      intro i j x
      exact schemeFieldBaseChangeCoverLocalEquiv_restrict_right
        base M (V i) (V j) I (t i) (t j) (hAffine j)
          (hOverlapAffine i j) x)

/-- A finite-free Čech base-change equivalence can be chosen together with
its defining chartwise restriction formula. -/
theorem exists_schemeModuleOpenSectionsFieldBaseChangeLinearEquivOfFiniteFreeCover_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : ι → X.Opens) (hcover : ⊤ ≤ ⨆ i, V i)
    (hAffine : ∀ i, IsAffine (V i : Scheme.{u}))
    (hOverlapAffine : ∀ i j, IsAffine ((V i ⊓ V j : X.Opens) : Scheme.{u}))
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : ∀ i,
      SheafOfModules.free (R := X.ringCatSheaf.over (V i)) I ≅
        M.over (V i)) :
    ∃ e :
      (L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) ≃ₗ[L]
        SchemeModuleOpenSectionsOver
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback
            (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) ⊤,
      ∀ (i : ι) (x : L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤),
        schemeModuleOpenSectionsRestrictionLinearMap
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback
            (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) le_top
          (e x) =
        schemeFieldBaseChangeCoverLocalEquiv base M (V i) I (t i) (hAffine i)
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M le_top) x) := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let VL : ι → (schemeFieldBaseChange (L := L) base).Opens :=
    fun i => g ⁻¹ᵁ V i
  have hcoverL : ⊤ ≤ ⨆ i, VL i := by
    have hV : ⨆ i, V i = ⊤ := top_unique hcover
    dsimp only [VL]
    rw [g.iSup_preimage_eq_top hV]
  let localEquiv := fun i => schemeFieldBaseChangeCoverLocalEquiv
    (K := K) (L := L) base M (V i) I (t i) (hAffine i)
  let overlapEquiv := fun i j => schemeFieldBaseChangeCoverOverlapEquiv
    (K := K) (L := L) base M (V i) (V j) I (t i) (hOverlapAffine i j)
  have hleft : ∀ i j x,
      schemeModuleOpenSectionsRestrictionLinearMap
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback g).obj M) inf_le_left
          (localEquiv i x) =
        overlapEquiv i j
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_left) x) := by
    intro i j x
    exact schemeFieldBaseChangeCoverLocalEquiv_restrict_left
      base M (V i) (V j) I (t i) (hAffine i) (hOverlapAffine i j) x
  have hright : ∀ i j x,
      schemeModuleOpenSectionsRestrictionLinearMap
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback g).obj M) inf_le_right
          (localEquiv j x) =
        overlapEquiv i j
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M inf_le_right) x) := by
    intro i j x
    exact schemeFieldBaseChangeCoverLocalEquiv_restrict_right
      base M (V i) (V j) I (t i) (t j) (hAffine j)
        (hOverlapAffine i j) x
  let e := schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents
    base (schemeFieldBaseChangeToField (L := L) base) M
    ((Scheme.Modules.pullback g).obj M) V VL hcover hcoverL
    localEquiv overlapEquiv hleft hright
  refine ⟨e, ?_⟩
  intro i x
  exact schemeModuleOpenSectionsBaseChangeLinearEquivOfFiniteCoverOfComponents_restrict
    base (schemeFieldBaseChangeToField (L := L) base) M
    ((Scheme.Modules.pullback g).obj M) V VL hcover hcoverL
    localEquiv overlapEquiv hleft hright i x

end

end PfaffianDescent
