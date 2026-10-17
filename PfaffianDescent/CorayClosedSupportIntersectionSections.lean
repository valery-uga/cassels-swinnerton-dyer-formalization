import PfaffianDescent.CorayClosedSupportSectionExtension

/-! SOURCE ONLY / UNVERIFIED. Closed support contained in U gives actual
restriction/extension equivalences on EVERY open W, with original ground
scalars. These equivalences and their naturality are constructed, not supplied.
The direct two-open gluing proof avoids transports through a restricted scheme.
-/

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem schemeModule_sections_intersection_restriction_bijective_of_closedSupport_subset
    {X : Scheme.{u}} (M : X.Modules) (U W : X.Opens) (C : Set X)
    (hC : IsClosed C) (hsupport : schemeModuleStalkSupport M ⊆ C)
    (hCU : C ⊆ U) :
    Function.Bijective (M.presheaf.map
      (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op) := by
  classical
  let V : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  have hzero (T : X.Opens) (hTV : T ≤ V) : Subsingleton Γ(M, T) := by
    apply schemeModule_sections_subsingleton_of_support_disjoint M T
    intro x hx hs
    have hxV : x ∉ C := hTV hx
    exact hxV (hsupport hs)
  have hcover : W ≤ (U ⊓ W) ⊔ (V ⊓ W) := by
    intro x hxW
    by_cases hxC : x ∈ C
    · exact Or.inl ⟨hCU hxC, hxW⟩
    · exact Or.inr ⟨hxC, hxW⟩
  constructor
  · intro s t hst
    let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
    letI : Subsingleton Γ(M, V ⊓ W) := hzero (V ⊓ W) inf_le_left
    exact F.eq_of_locally_eq₂
      (homOfLE (show U ⊓ W ≤ W from inf_le_right))
      (homOfLE (show V ⊓ W ≤ W from inf_le_right))
      hcover s t hst (Subsingleton.elim _ _)
  · intro s
    let A : Bool → X.Opens := fun b => cond b (U ⊓ W) (V ⊓ W)
    let sf : (b : Bool) → Γ(M, A b) := fun b => by
      cases b
      · exact 0
      · exact s
    have hA : ∀ b, A b ≤ W := by
      intro b
      cases b <;> exact inf_le_right
    have hcoverA : W ≤ ⨆ b, A b :=
      hcover.trans (sup_le (le_iSup A true) (le_iSup A false))
    have hcompat : ∀ a b,
        M.val.map (homOfLE (show A a ⊓ A b ≤ A a from inf_le_left)).op (sf a) =
        M.val.map (homOfLE (show A a ⊓ A b ≤ A b from inf_le_right)).op (sf b) := by
      intro a b
      cases a <;> cases b
      · rfl
      · exact @Subsingleton.elim Γ(M, (V ⊓ W) ⊓ (U ⊓ W))
          (hzero _ (inf_le_left.trans inf_le_left)) _ _
      · exact @Subsingleton.elim Γ(M, (U ⊓ W) ⊓ (V ⊓ W))
          (hzero _ (inf_le_right.trans inf_le_left)) _ _
      · rfl
    obtain ⟨t, ht, _⟩ := schemeModuleSections_glue M W A hA hcoverA sf hcompat
    exact ⟨t, ht true⟩

def schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (U W : X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    SchemeModuleOpenSectionsOver pi M W ≃ₗ[K]
      SchemeModuleOpenSectionsOver pi M (U ⊓ W) :=
  LinearEquiv.ofBijective
    (schemeModuleOpenSectionsRestrictionLinearMap pi M
      (show U ⊓ W ≤ W from inf_le_right))
    (schemeModule_sections_intersection_restriction_bijective_of_closedSupport_subset
      M U W C hC hsupport hCU)

theorem schemeModule_groundRestriction_comp
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    {A B D : X.Opens} (hBA : B ≤ A) (hDB : D ≤ B)
    (s : SchemeModuleOpenSectionsOver pi M A) :
    schemeModuleOpenSectionsRestrictionLinearMap pi M hDB
        (schemeModuleOpenSectionsRestrictionLinearMap pi M hBA s) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M (hDB.trans hBA) s := by
  change M.val.map (homOfLE hDB).op (M.val.map (homOfLE hBA).op s) =
    M.val.map (homOfLE (hDB.trans hBA)).op s
  exact (PresheafOfModules.map_comp_apply M.val
    (homOfLE hBA).op (homOfLE hDB).op s).symm

theorem schemeModule_groundIntersectionExtension_naturality
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (U : X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U)
    {W V : X.Opens} (hVW : V ≤ W)
    (s : SchemeModuleOpenSectionsOver pi M (U ⊓ W)) :
    schemeModuleOpenSectionsRestrictionLinearMap pi M
        (show U ⊓ V ≤ V from inf_le_right)
        (schemeModuleOpenSectionsRestrictionLinearMap pi M hVW
          ((schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset
            pi M U W C hC hsupport hCU).symm s)) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M (inf_le_inf_left U hVW) s := by
  let e := schemeModule_groundIntersectionSectionsEquiv_of_closedSupport_subset
    pi M U W C hC hsupport hCU
  calc
    _ = schemeModuleOpenSectionsRestrictionLinearMap pi M
        (inf_le_right.trans hVW) (e.symm s) :=
      schemeModule_groundRestriction_comp pi M hVW inf_le_right (e.symm s)
    _ = schemeModuleOpenSectionsRestrictionLinearMap pi M (inf_le_inf_left U hVW)
        (schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right (e.symm s)) :=
      (schemeModule_groundRestriction_comp pi M inf_le_right
        (inf_le_inf_left U hVW) (e.symm s)).symm
    _ = schemeModuleOpenSectionsRestrictionLinearMap pi M (inf_le_inf_left U hVW) s := by
      exact congrArg (schemeModuleOpenSectionsRestrictionLinearMap pi M
        (inf_le_inf_left U hVW)) (e.apply_symm_apply s)

end PfaffianDescent.Coray
