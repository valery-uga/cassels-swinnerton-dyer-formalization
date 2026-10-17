import PfaffianDescent.CorayStalkSupportSectionVanishing
import PfaffianDescent.SchemeModuleSectionGluing
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! Literal extension by zero from an open containing actual closed stalk
support. Restrictions are proved bijective by actual sheaf gluing; original
ground scalar actions are retained via existing literal restriction maps.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Sections extend uniquely from U when U and V cover and every actual
stalk over V is zero. Overlap compatibility is proved from actual germs;
no restriction-surjectivity or section-zero certificate is assumed. -/
theorem schemeModule_sections_restriction_bijective_of_zero_complement
    {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
    (hcover : ⊤ ≤ U ⊔ V)
    (hV : ∀ x : X, x ∈ V → x ∉ schemeModuleStalkSupport M) :
    Function.Bijective
      (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  classical
  have hzero (W : X.Opens) (hWV : W ≤ V) : Subsingleton Γ(M, W) := by
    apply schemeModule_sections_subsingleton_of_support_disjoint M W
    intro x hx
    exact hV x (hWV hx)
  constructor
  · intro s t hst
    let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
    letI : Subsingleton Γ(M, V) := hzero V le_rfl
    exact F.eq_of_locally_eq₂
      (homOfLE (show U ≤ ⊤ from le_top))
      (homOfLE (show V ≤ ⊤ from le_top)) hcover s t hst (Subsingleton.elim _ _)
  · intro s
    let W : Bool → X.Opens := fun b => cond b U V
    let sf : (b : Bool) → Γ(M, W b) := fun b => by
      cases b
      · exact 0
      · exact s
    have hW : ∀ b, W b ≤ ⊤ := fun _ => le_top
    have hwcover : ⊤ ≤ ⨆ b, W b :=
      hcover.trans (sup_le (le_iSup W true) (le_iSup W false))
    have hcompat : ∀ i j,
        M.val.map (homOfLE (show W i ⊓ W j ≤ W i from inf_le_left)).op (sf i) =
        M.val.map (homOfLE (show W i ⊓ W j ≤ W j from inf_le_right)).op (sf j) := by
      intro i j
      cases i <;> cases j
      · rfl
      · exact @Subsingleton.elim Γ(M, V ⊓ U) (hzero (V ⊓ U) inf_le_left) _ _
      · exact @Subsingleton.elim Γ(M, U ⊓ V) (hzero (U ⊓ V) inf_le_right) _ _
      · rfl
    obtain ⟨t, ht, _⟩ := schemeModuleSections_glue M ⊤ W hW hwcover sf hcompat
    exact ⟨t, ht true⟩

/-- Literal global sections restrict bijectively to an open containing an
actual closed set that contains every actual nonzero stalk. The complement
and overlap vanish by actual stalk extensionality, and sections glue with zero. -/
theorem schemeModule_sections_restriction_bijective_of_closedSupport_subset
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (C : Set X)
    (hC : IsClosed C) (hsupport : schemeModuleStalkSupport M ⊆ C)
    (hCU : C ⊆ U) :
    Function.Bijective
      (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  let V : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  have hcover : ⊤ ≤ U ⊔ V := by
    intro x hx
    change x ∈ U ∨ x ∉ C
    by_cases hxC : x ∈ C
    · exact Or.inl (hCU hxC)
    · exact Or.inr hxC
  apply schemeModule_sections_restriction_bijective_of_zero_complement M U V hcover
  intro x hx hs
  change x ∉ C at hx
  exact hx (hsupport hs)

/-- The actual restriction/extension is a linear equivalence for the
ORIGINAL ground action supplied by the original scheme structure morphism.
It is constructed from the genuine bijectivity proof, not supplied as a map. -/
def schemeModule_groundOpenSectionsEquiv_of_closedSupport_subset
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (U : X.Opens) (C : Set X)
    (hC : IsClosed C) (hsupport : schemeModuleStalkSupport M ⊆ C)
    (hCU : C ⊆ U) :
    SchemeModuleOpenSectionsOver p M ⊤ ≃ₗ[K] SchemeModuleOpenSectionsOver p M U :=
  LinearEquiv.ofBijective
    (schemeModuleOpenSectionsRestrictionLinearMap p M (show U ≤ ⊤ from le_top))
    (schemeModule_sections_restriction_bijective_of_closedSupport_subset M U C hC hsupport hCU)

/-- Literal morphism-valued GLOBAL module sections also identify with the
original open section module. The actual original-K global-to-top bridge
and actual proved restriction equivalence supply the entire comparison. -/
def schemeModule_groundGlobalSectionsEquiv_of_closedSupport_subset
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (U : X.Opens) (C : Set X)
    (hC : IsClosed C) (hsupport : schemeModuleStalkSupport M ⊆ C)
    (hCU : C ⊆ U) :
    SchemeModuleGlobalSectionsOver p M ≃ₗ[K] SchemeModuleOpenSectionsOver p M U :=
  (schemeModuleGlobalSectionsLinearEquivOpenTop p M).trans
    (schemeModule_groundOpenSectionsEquiv_of_closedSupport_subset p M U C hC hsupport hCU)

end PfaffianDescent.Coray
