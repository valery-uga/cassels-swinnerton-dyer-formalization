import PfaffianDescent.SchemeModuleSectionGluing
import PfaffianDescent.SchemeAffineFunctions

/-!
# Global module sections as a cover equalizer

The sheaf condition identifies sections on an open with compatible tuples of
sections on a cover.  This file records that identification as an additive
equivalence, in preparation for applying flat base change to a finite Cech
equalizer.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Opposite

universe u v

noncomputable section

variable {K : Type u} [Field K]

/-- The ground-field functions on an open, obtained by restricting the
functions supplied by the structure morphism. -/
noncomputable def schemeOpenBaseRingHom {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp
    (affineFunctionHom p)

@[simp]
theorem schemeOpenBaseRingHom_top_apply {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (c : K) :
    schemeOpenBaseRingHom p ⊤ c = affineFunctionHom p c := by
  change X.presheaf.map
      (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op
        (affineFunctionHom p c) = affineFunctionHom p c
  simpa using congr_fun (X.presheaf.map_id (op ⊤)) (affineFunctionHom p c)

/-- Sections of a module sheaf on an open, regarded as a vector space over
the ground field of the scheme. -/
def SchemeModuleOpenSectionsOver {X : Scheme.{u}}
    (_p : X ⟶ Spec (.of K)) (M : X.Modules) (U : X.Opens) :=
  Γ(M, U)

noncomputable instance {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) :
    AddCommGroup (SchemeModuleOpenSectionsOver p M U) :=
  inferInstanceAs (AddCommGroup Γ(M, U))

noncomputable instance {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) :
    Module K (SchemeModuleOpenSectionsOver p M U) :=
  Module.compHom Γ(M, U) (schemeOpenBaseRingHom p U)

/-- Restriction of module sections is linear over the ground field. -/
noncomputable def schemeModuleOpenSectionsRestrictionLinearMap
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U) :
    SchemeModuleOpenSectionsOver p M U →ₗ[K]
      SchemeModuleOpenSectionsOver p M V where
  toFun := M.val.map (homOfLE hVU).op
  map_add' := (M.val.map (homOfLE hVU).op).hom.map_add
  map_smul' c s := by
    let rU : Γ(X, U) := schemeOpenBaseRingHom p U c
    let rV : Γ(X, V) := schemeOpenBaseRingHom p V c
    let sU : Γ(M, U) := s
    change M.presheaf.map (homOfLE hVU).op (rU • sU) =
      rV • M.presheaf.map (homOfLE hVU).op sU
    rw [M.map_smul]
    congr 1
    exact (CategoryTheory.congr_fun
      (X.presheaf.map_comp
        (homOfLE (show U ≤ ⊤ from le_top)).op (homOfLE hVU).op)
      (affineFunctionHom p c)).symm

/-- The first face map in the pairwise Cech equalizer. -/
noncomputable def schemeModuleCoverLeftRestrictionLinearMap
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} (V : ι → X.Opens) :
    (∀ i, SchemeModuleOpenSectionsOver p M (V i)) →ₗ[K]
      (∀ i j, SchemeModuleOpenSectionsOver p M (V i ⊓ V j)) where
  toFun s i j := schemeModuleOpenSectionsRestrictionLinearMap p M inf_le_left (s i)
  map_add' s t := by
    ext i j
    exact (schemeModuleOpenSectionsRestrictionLinearMap p M inf_le_left).map_add _ _
  map_smul' c s := by
    ext i j
    exact (schemeModuleOpenSectionsRestrictionLinearMap p M inf_le_left).map_smul _ _

/-- The second face map in the pairwise Cech equalizer. -/
noncomputable def schemeModuleCoverRightRestrictionLinearMap
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} (V : ι → X.Opens) :
    (∀ i, SchemeModuleOpenSectionsOver p M (V i)) →ₗ[K]
      (∀ i j, SchemeModuleOpenSectionsOver p M (V i ⊓ V j)) where
  toFun s i j := schemeModuleOpenSectionsRestrictionLinearMap p M inf_le_right (s j)
  map_add' s t := by
    ext i j
    exact (schemeModuleOpenSectionsRestrictionLinearMap p M inf_le_right).map_add _ _
  map_smul' c s := by
    ext i j
    exact (schemeModuleOpenSectionsRestrictionLinearMap p M inf_le_right).map_smul _ _

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type v}
    (U : X.Opens) (V : ι → X.Opens) (hV : ∀ i, V i ≤ U)
    (hcover : U ≤ ⨆ i, V i)

/-- Tuples of local sections satisfying the pairwise overlap condition. -/
def schemeModuleCompatibleCoverSections :
    AddSubgroup (∀ i, Γ(M, V i)) where
  carrier := {s | ∀ i j,
    M.val.map (homOfLE (show V i ⊓ V j ≤ V i from inf_le_left)).op (s i) =
      M.val.map (homOfLE (show V i ⊓ V j ≤ V j from inf_le_right)).op (s j)}
  zero_mem' := by
    intro i j
    change
      (M.val.map
        (homOfLE (show V i ⊓ V j ≤ V i from inf_le_left)).op).hom 0 =
      (M.val.map
        (homOfLE (show V i ⊓ V j ≤ V j from inf_le_right)).op).hom 0
    rw [(M.val.map _).hom.map_zero, (M.val.map _).hom.map_zero]
    rfl
  add_mem' := by
    intro s t hs ht i j
    let f := (M.val.map
      (homOfLE (show V i ⊓ V j ≤ V i from inf_le_left)).op).hom
    let g := (M.val.map
      (homOfLE (show V i ⊓ V j ≤ V j from inf_le_right)).op).hom
    change
      f (s i + t i) = g (s j + t j)
    exact (f.map_add (s i) (t i)).trans
      ((congrArg₂ (fun a b : Γ(M, V i ⊓ V j) => a + b)
        (show f (s i) = g (s j) from hs i j)
        (show f (t i) = g (t j) from ht i j)).trans
          (g.map_add (s j) (t j)).symm)
  neg_mem' := by
    intro s hs i j
    let f := (M.val.map
      (homOfLE (show V i ⊓ V j ≤ V i from inf_le_left)).op).hom
    let g := (M.val.map
      (homOfLE (show V i ⊓ V j ≤ V j from inf_le_right)).op).hom
    change
      f (-s i) = g (-s j)
    exact (f.map_neg (s i)).trans
      ((congrArg (fun a : Γ(M, V i ⊓ V j) => -a)
        (show f (s i) = g (s j) from hs i j)).trans
          (g.map_neg (s j)).symm)

/-- Restriction of one section to a compatible tuple on the cover. -/
noncomputable def schemeModuleSectionToCompatibleCoverSections :
    Γ(M, U) →+
      schemeModuleCompatibleCoverSections M V where
  toFun s :=
    ⟨fun i => M.val.map (homOfLE (hV i)).op s, by
      intro i j
      exact (PresheafOfModules.map_comp_apply M.val
        (homOfLE (hV i)).op (homOfLE inf_le_left).op s).symm.trans
          (PresheafOfModules.map_comp_apply M.val
            (homOfLE (hV j)).op (homOfLE inf_le_right).op s)⟩
  map_zero' := by
    ext i
    exact map_zero _
  map_add' s t := by
    ext i
    exact map_add _ _ _

/-- The section obtained by gluing a compatible tuple. -/
noncomputable def schemeModuleCompatibleCoverSectionsGlue
    (s : schemeModuleCompatibleCoverSections M V) : Γ(M, U) :=
  Classical.choose
    (schemeModuleSections_glue M U V hV hcover s s.property)

theorem schemeModuleCompatibleCoverSectionsGlue_restrict
    (s : schemeModuleCompatibleCoverSections M V) (i : ι) :
    M.val.map (homOfLE (hV i)).op
        (schemeModuleCompatibleCoverSectionsGlue M U V hV hcover s) =
      s.1 i :=
  (Classical.choose_spec
    (schemeModuleSections_glue M U V hV hcover s s.property)).1 i

/-- Gluing compatible tuples is additive. -/
noncomputable def schemeModuleCompatibleCoverSectionsGlueHom :
    schemeModuleCompatibleCoverSections M V →+ Γ(M, U) where
  toFun := schemeModuleCompatibleCoverSectionsGlue M U V hV hcover
  map_zero' := by
    apply schemeModuleSections_ext M U V hV hcover
    intro i
    rw [schemeModuleCompatibleCoverSectionsGlue_restrict]
    change (0 : Γ(M, V i)) = M.val.map (homOfLE (hV i)).op 0
    exact ((M.val.map (homOfLE (hV i)).op).hom.map_zero).symm
  map_add' s t := by
    apply schemeModuleSections_ext M U V hV hcover
    intro i
    rw [schemeModuleCompatibleCoverSectionsGlue_restrict]
    let f := (M.val.map (homOfLE (hV i)).op).hom
    change s.1 i + t.1 i = f
      (schemeModuleCompatibleCoverSectionsGlue M U V hV hcover s +
        schemeModuleCompatibleCoverSectionsGlue M U V hV hcover t)
    exact (congrArg₂ (fun a b : Γ(M, V i) => a + b)
      (schemeModuleCompatibleCoverSectionsGlue_restrict M U V hV hcover s i).symm
      (schemeModuleCompatibleCoverSectionsGlue_restrict M U V hV hcover t i).symm).trans
        (f.map_add
          (schemeModuleCompatibleCoverSectionsGlue M U V hV hcover s)
          (schemeModuleCompatibleCoverSectionsGlue M U V hV hcover t)).symm

/-- The sheaf condition as an additive equivalence between global sections
and the pairwise Cech equalizer of a cover. -/
noncomputable def schemeModuleSectionsAddEquivCompatibleCoverSections :
    Γ(M, U) ≃+
      schemeModuleCompatibleCoverSections M V where
  toFun := schemeModuleSectionToCompatibleCoverSections M U V hV
  invFun := schemeModuleCompatibleCoverSectionsGlueHom M U V hV hcover
  left_inv s := by
    apply schemeModuleSections_ext M U V hV hcover
    intro i
    change M.val.map (homOfLE (hV i)).op
        (schemeModuleCompatibleCoverSectionsGlue M U V hV hcover
          (schemeModuleSectionToCompatibleCoverSections M U V hV s)) =
      M.val.map (homOfLE (hV i)).op s
    rw [schemeModuleCompatibleCoverSectionsGlue_restrict]
    rfl
  right_inv s := by
    ext i
    exact schemeModuleCompatibleCoverSectionsGlue_restrict M U V hV hcover s i
  map_add' := map_add _

/-- The sheaf condition as the linear equalizer presentation used by flat
base change. -/
noncomputable def schemeModuleOpenSectionsLinearEquivCoverEqLocus
    (p : X ⟶ Spec (.of K)) :
    SchemeModuleOpenSectionsOver p M U ≃ₗ[K]
      LinearMap.eqLocus
        (schemeModuleCoverLeftRestrictionLinearMap p M V)
        (schemeModuleCoverRightRestrictionLinearMap p M V) where
  toFun s := ⟨fun i =>
    schemeModuleOpenSectionsRestrictionLinearMap p M (hV i) s, by
      ext i j
      exact (PresheafOfModules.map_comp_apply M.val
        (homOfLE (hV i)).op (homOfLE inf_le_left).op s).symm.trans
          (PresheafOfModules.map_comp_apply M.val
            (homOfLE (hV j)).op (homOfLE inf_le_right).op s)⟩
  invFun s := schemeModuleCompatibleCoverSectionsGlue M U V hV hcover
    ⟨s.1, by
      intro i j
      exact congrFun (congrFun s.property i) j⟩
  left_inv s := by
    apply schemeModuleSections_ext M U V hV hcover
    intro i
    rw [schemeModuleCompatibleCoverSectionsGlue_restrict]
    rfl
  right_inv s := by
    ext i
    exact schemeModuleCompatibleCoverSectionsGlue_restrict M U V hV hcover
      ⟨s.1, by
        intro a b
        exact congrFun (congrFun s.property a) b⟩ i
  map_add' s t := by
    ext i
    exact (schemeModuleOpenSectionsRestrictionLinearMap p M (hV i)).map_add s t
  map_smul' c s := by
    ext i
    exact (schemeModuleOpenSectionsRestrictionLinearMap p M (hV i)).map_smul c s

end

end PfaffianDescent
