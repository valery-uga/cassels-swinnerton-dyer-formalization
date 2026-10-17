import PfaffianDescent.VoisinFieldBaseChangeCech
import PfaffianDescent.VoisinFieldBaseChangeGlobalComparison
import PfaffianDescent.VoisinFixedLinearSystemUniversalFamily

/-!
# Field base change from a finite-free affine cover

This file packages the Čech field-base-change theorem in the exact form
provided by `SchemeModuleFiniteFreeAffineCover`.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace SchemeModuleFiniteFreeAffineCover

/-- Pairwise intersections in a finite-free affine cover are affine when the
structure morphism is separated. -/
theorem overlapAffine_of_isSeparated
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base]
    {M : X.Modules} {I : Type u}
    (C : SchemeModuleFiniteFreeAffineCover M I) (i j : C.ι) :
    IsAffine ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) := by
  have hUi : IsAffineOpen (C.U i) := C.affine i
  have hUj : IsAffineOpen (C.U j) := C.affine j
  exact (isAffineHom_diagonal_iff (f := base)).mp inferInstance
    ⊤ (isAffineOpen_top _) (C.U i) (by simp) (C.U j) (by simp) hUi hUj

private theorem exists_openSectionsFieldBaseChangeLinearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι] :
    ∃ e :
      (L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) ≃ₗ[L]
        SchemeModuleOpenSectionsOver
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback
            (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) ⊤,
      ∀ (i : C.ι) (x : L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤),
        schemeModuleOpenSectionsRestrictionLinearMap
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback
            (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) le_top
          (e x) =
        schemeFieldBaseChangeCoverLocalEquiv base M (C.U i) I
          (C.trivialization i) (C.affine i)
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M le_top) x) := by
  exact
    exists_schemeModuleOpenSectionsFieldBaseChangeLinearEquivOfFiniteFreeCover_restrict
      (K := K) (L := L) (I := I) base M C.U
      (by rw [C.covers]) C.affine (C.overlapAffine_of_isSeparated base)
      C.trivialization

private opaque openSectionsFieldBaseChangeData
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι] :
    {e :
      (L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) ≃ₗ[L]
        SchemeModuleOpenSectionsOver
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback
            (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) ⊤ //
      ∀ (i : C.ι) (x : L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤),
        schemeModuleOpenSectionsRestrictionLinearMap
          (schemeFieldBaseChangeToField (L := L) base)
          ((Scheme.Modules.pullback
            (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) le_top
          (e x) =
        schemeFieldBaseChangeCoverLocalEquiv base M (C.U i) I
          (C.trivialization i) (C.affine i)
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M le_top) x)} := by
  let h := exists_openSectionsFieldBaseChangeLinearEquiv
    (K := K) (L := L) base M C
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Open-section field base change obtained canonically from a finite-free
affine cover. -/
noncomputable def openSectionsFieldBaseChangeLinearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι] :
    (L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) ≃ₗ[L]
      SchemeModuleOpenSectionsOver
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) ⊤ :=
  (openSectionsFieldBaseChangeData base M C).1

/-- The chosen finite-free-cover equivalence is characterized chartwise by
the canonical local pullback equivalence. -/
theorem openSectionsFieldBaseChangeLinearEquiv_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    (i : C.ι) (x : L ⊗[K] SchemeModuleOpenSectionsOver base M ⊤) :
    schemeModuleOpenSectionsRestrictionLinearMap
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) le_top
        (C.openSectionsFieldBaseChangeLinearEquiv base M x) =
      schemeFieldBaseChangeCoverLocalEquiv base M (C.U i) I
        (C.trivialization i) (C.affine i)
        (TensorProduct.AlgebraTensorModule.lTensor L L
          (schemeModuleOpenSectionsRestrictionLinearMap base M le_top) x) := by
  exact (openSectionsFieldBaseChangeData base M C).2 i x

/-- On pure tensors, the chosen global open-section equivalence is exactly
scalar multiplication of the intrinsic pullback section. -/
theorem openSectionsFieldBaseChangeLinearEquiv_tmul_eq_smul_pullback
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    (c : L) (s : SchemeModuleOpenSectionsOver base M ⊤) :
    C.openSectionsFieldBaseChangeLinearEquiv base M (c ⊗ₜ[K] s) =
      c • schemeFieldBaseChangeOpenPullbackSection (L := L) base M ⊤ s := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let pL := schemeFieldBaseChangeToField (L := L) base
  let ML := (Scheme.Modules.pullback g).obj M
  let rhs0 : SchemeModuleOpenSectionsOver pL ML ⊤ :=
    schemeFieldBaseChangeOpenPullbackSection (L := L) base M ⊤ s
  let rhs : SchemeModuleOpenSectionsOver pL ML ⊤ := c • rhs0
  change C.openSectionsFieldBaseChangeLinearEquiv base M (c ⊗ₜ[K] s) = rhs
  let VL : C.ι → (schemeFieldBaseChange (L := L) base).Opens :=
    fun i => g ⁻¹ᵁ C.U i
  have hcoverL : ⊤ ≤ ⨆ i, VL i := by
    dsimp only [VL]
    rw [g.iSup_preimage_eq_top C.covers]
  apply schemeModuleSections_ext ML ⊤ VL (fun _ ↦ le_top) hcoverL
  intro i
  letI : IsAffine (C.U i : Scheme.{u}) := C.affine i
  change schemeModuleOpenSectionsRestrictionLinearMap pL ML le_top
      (C.openSectionsFieldBaseChangeLinearEquiv base M (c ⊗ₜ[K] s)) =
    schemeModuleOpenSectionsRestrictionLinearMap pL ML le_top rhs
  dsimp only [pL, ML, g, VL]
  have he := C.openSectionsFieldBaseChangeLinearEquiv_restrict
    (L := L) base M i (c ⊗ₜ[K] s)
  rw [he]
  rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
  rw [schemeFieldBaseChangeCoverLocalEquiv_tmul_eq_smul_pullback]
  change _ = schemeModuleOpenSectionsRestrictionLinearMap
    (schemeFieldBaseChangeToField (L := L) base)
    ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) le_top (c • rhs0)
  rw [map_smul]
  congr 1
  have hnat := schemeFieldBaseChangeOpenPullbackSection_restrict
    (L := L) base M (U := (⊤ : X.Opens)) (W := C.U i) le_top s
  exact hnat.symm

/-- Morphism-valued global sections commute with field extension for a module
equipped with a finite-free affine cover on a separated scheme. -/
noncomputable def globalSectionsFieldBaseChangeLinearEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι] :
    (L ⊗[K] SchemeModuleGlobalSectionsOver base M) ≃ₗ[L]
      SchemeModuleGlobalSectionsOver
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) :=
  (schemeModuleGlobalSectionsLinearEquivOpenTop base M).baseChange
      K L (SchemeModuleGlobalSectionsOver base M)
        (SchemeModuleOpenSectionsOver base M ⊤) ≪≫ₗ
    C.openSectionsFieldBaseChangeLinearEquiv base M ≪≫ₗ
      (schemeModuleGlobalSectionsLinearEquivOpenTop
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The finite-cover global equivalence agrees on pure tensors with the
literal canonical pullback of morphism-valued global sections. -/
theorem globalSectionsFieldBaseChangeLinearEquiv_tmul_eq_smul_pullback
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    (c : L) (s : SchemeModuleGlobalSectionsOver base M) :
    C.globalSectionsFieldBaseChangeLinearEquiv base M (c ⊗ₜ[K] s) =
      c • (schemeModuleGlobalSectionsOverEquivSections
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm
        (BundleSectionZeroLocus.pullbackSection
          (schemeFieldBaseChangeToOriginal (L := L) base) M
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison
            (schemeFieldBaseChangeToOriginal (L := L) base))
          (schemeModuleGlobalSectionsOverEquivSections base M s)) := by
  let σ := schemeModuleGlobalSectionsOverEquivSections base M s
  let τ := BundleSectionZeroLocus.pullbackSection
    (schemeFieldBaseChangeToOriginal (L := L) base) M
    (BundleSectionZeroLocus.isIso_pullbackUnitComparison
      (schemeFieldBaseChangeToOriginal (L := L) base)) σ
  let eK := schemeModuleGlobalSectionsLinearEquivOpenTop base M
  let eL := schemeModuleGlobalSectionsLinearEquivOpenTop
    (schemeFieldBaseChangeToField (L := L) base)
    ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
  let target := (schemeModuleGlobalSectionsOverEquivSections
    (schemeFieldBaseChangeToField (L := L) base)
    ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm τ
  have hsK : eK s = schemeModuleSectionsEquivTop M σ := rfl
  have htL : eL target = schemeModuleSectionsEquivTop
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) τ := by
    change schemeModuleSectionsEquivTop _
      (schemeModuleGlobalSectionsOverEquivSections _ _
        ((schemeModuleGlobalSectionsOverEquivSections _ _).symm τ)) = _
    rw [(schemeModuleGlobalSectionsOverEquivSections _ _).apply_symm_apply]
  apply eL.injective
  unfold globalSectionsFieldBaseChangeLinearEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, map_smul]
  dsimp only [eL]
  rw [(schemeModuleGlobalSectionsLinearEquivOpenTop
    (schemeFieldBaseChangeToField (L := L) base)
    ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).apply_symm_apply]
  change C.openSectionsFieldBaseChangeLinearEquiv base M
      (c ⊗ₜ[K] eK s) = c • eL target
  rw [hsK, htL]
  refine (C.openSectionsFieldBaseChangeLinearEquiv_tmul_eq_smul_pullback
    base M c (schemeModuleSectionsEquivTop M σ)).trans ?_
  exact congrArg (fun z : SchemeModuleOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base)
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M) ⊤ => c • z)
    (schemeFieldBaseChangeOpenPullback_top_global (L := L) base M σ)

/-- The finite-cover equivalence is the literal canonical global-sections
field-base-change map. -/
theorem globalSectionsFieldBaseChangeLinearEquiv_toLinearMap_eq_canonical
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    (C.globalSectionsFieldBaseChangeLinearEquiv base M).toLinearMap =
      schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base M := by
  apply (Module.finBasis K
    (SchemeModuleGlobalSectionsOver base M)).baseChange L |>.ext
  intro i
  rw [Module.Basis.baseChange_apply]
  let b := Module.finBasis K
    (SchemeModuleGlobalSectionsOver base M) i
  let target := (schemeModuleGlobalSectionsOverEquivSections
    (schemeFieldBaseChangeToField (L := L) base)
    ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm
    (BundleSectionZeroLocus.pullbackSection
      (schemeFieldBaseChangeToOriginal (L := L) base) M
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison
        (schemeFieldBaseChangeToOriginal (L := L) base))
      (schemeModuleGlobalSectionsOverEquivSections base M b))
  change C.globalSectionsFieldBaseChangeLinearEquiv base M (1 ⊗ₜ[K] b) =
    schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base M
      (1 ⊗ₜ[K] b)
  calc
    _ = 1 • target :=
      C.globalSectionsFieldBaseChangeLinearEquiv_tmul_eq_smul_pullback
        base M 1 b
    _ = target := one_smul _ _
    _ = _ := (schemeModuleGlobalSectionsFieldBaseChangeLinearMap_one_tmul_finBasis
      (L := L) base M i).symm

/-- The canonical morphism-valued global-sections map is bijective for a
module admitting a finite-free affine cover on a separated scheme. -/
theorem globalSectionsFieldBaseChangeLinearMap_bijective
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    Function.Bijective
      (schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base M) := by
  rw [← C.globalSectionsFieldBaseChangeLinearEquiv_toLinearMap_eq_canonical
    (L := L) base M]
  exact (C.globalSectionsFieldBaseChangeLinearEquiv base M).bijective

/-- The canonical equivalence obtained from canonical-map bijectivity is
the finite-cover equivalence constructed by Čech gluing. -/
theorem canonicalGlobalSectionsFieldBaseChangeLinearEquiv_eq
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [IsSeparated base]
    (M : X.Modules) {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    schemeModuleGlobalSectionsFieldBaseChangeLinearEquiv (L := L) base M
        (C.globalSectionsFieldBaseChangeLinearMap_bijective (L := L) base M) =
      C.globalSectionsFieldBaseChangeLinearEquiv base M := by
  ext v
  change schemeModuleGlobalSectionsFieldBaseChangeLinearMap (L := L) base M v = _
  rw [← C.globalSectionsFieldBaseChangeLinearEquiv_toLinearMap_eq_canonical
    (L := L) base M]
  rfl

end SchemeModuleFiniteFreeAffineCover

end

end PfaffianDescent
