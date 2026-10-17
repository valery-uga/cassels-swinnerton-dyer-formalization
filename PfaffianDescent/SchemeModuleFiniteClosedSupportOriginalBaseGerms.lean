import PfaffianDescent.SchemeModuleOriginalBaseWeightedStalk
import PfaffianDescent.CorayStalkSupportSectionVanishing
import PfaffianDescent.SchemeModuleSectionGluing
import Mathlib.Topology.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Actual sections of a sheaf module with finite closed-point stalk support
decompose by the original germs into the SAME original-K native stalks.
The map is proved bijective from actual sheaf gluing, with no decomposition
certificate or affine-neighborhood hypothesis. Depends on UNVERIFIED
original-base-weighted-stalk003 and staged support-section vanishing.
SOURCE ONLY / UNVERIFIED. Root alone compiles. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BigOperators
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original top-section germs, with the SAME original K-action
in every target native stalk. This does not choose scalar coordinates. -/
def schemeModuleOriginalBaseTopGermsLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X) :
    SchemeModuleOpenSectionsOver pi M ⊤ →ₗ[K]
      (∀ x : C, SchemeModuleStalkOver pi M x.1) :=
  LinearMap.pi (fun x : C =>
    schemeModuleOriginalBaseGermLinearMap pi M x.1 ⊤ trivial)

theorem schemeModuleOriginalBaseTopGermsLinearMap_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X)
    (s : SchemeModuleOpenSectionsOver pi M ⊤) (x : C) :
    schemeModuleOriginalBaseTopGermsLinearMap pi M C s x =
      (show SchemeModuleStalkOver pi M x.1 from M.presheaf.germ ⊤ x.1 trivial s) := rfl

/-- Arbitrary elements in the finitely many closed support stalks arise
from one actual section. For each center, its actual germ representative
is restricted away from every OTHER support point; the overlaps and the
support complement have zero stalks, so these sections glue with zero.
Injectivity is actual sheaf stalk extensionality. -/
theorem schemeModuleOriginalBaseTopGermsLinearMap_bijective
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X)
    (hC : C.Finite) (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupport : schemeModuleStalkSupport M ⊆ C) :
    Function.Bijective (schemeModuleOriginalBaseTopGermsLinearMap pi M C) := by
  classical
  have hDclosed (D : Set X) (hD : D ⊆ C) : IsClosed D := by
    rw [← Set.biUnion_of_singleton D]
    exact (hC.subset hD).isClosed_biUnion (fun x hx => hclosed x (hD hx))
  let V : X.Opens := ⟨Cᶜ, (hDclosed C Set.Subset.rfl).isOpen_compl⟩
  constructor
  · intro s t hst
    let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
    apply TopCat.Presheaf.section_ext F ⊤ s t
    intro x hx
    by_cases hxC : x ∈ C
    · exact congrFun hst ⟨x, hxC⟩
    · have hxoff : x ∉ schemeModuleStalkSupport M := fun h => hxC (hsupport h)
      letI : Subsingleton (M.presheaf.stalk x) :=
        not_nontrivial_iff_subsingleton.mp hxoff
      exact Subsingleton.elim _ _
  · intro z
    have hrep (x : C) : ∃ (U : X.Opens) (hx : x.1 ∈ U) (s : Γ(M, U)),
        M.presheaf.germ U x.1 hx s = z x :=
      M.presheaf.exists_germ_eq (z x)
    choose U hx s hs using hrep
    let W (x : C) : X.Opens := U x ⊓
      ⟨(C \ {x.1})ᶜ, (hDclosed (C \ {x.1}) Set.diff_subset).isOpen_compl⟩
    have hxW (x : C) : x.1 ∈ W x := by
      refine ⟨hx x, ?_⟩
      simp
    have hcenter (x : C) (y : X) (hyC : y ∈ C) (hyW : y ∈ W x) : y = x.1 := by
      have hyother : y ∉ C \ {x.1} := hyW.2
      by_contra hne
      exact hyother ⟨hyC, by simpa only [Set.mem_singleton_iff] using hne⟩
    let A : Option C → X.Opens := fun i => match i with
      | none => V
      | some x => W x
    let t : ∀ i, Γ(M, A i) := fun i => match i with
      | none => 0
      | some x => M.val.map (homOfLE (show W x ≤ U x from inf_le_left)).op (s x)
    have hcover : ⊤ ≤ ⨆ i, A i := by
      intro y hy
      by_cases hyC : y ∈ C
      · exact (le_iSup A (some ⟨y, hyC⟩)) (hxW ⟨y, hyC⟩)
      · exact (le_iSup A none) (show y ∈ V from hyC)
    have hzero (B : X.Opens) (hBV : B ≤ V) : Subsingleton Γ(M, B) := by
      apply schemeModule_sections_subsingleton_of_support_disjoint M B
      intro y hy hyS
      have hyoff : y ∉ C := hBV hy
      exact hyoff (hsupport hyS)
    have hcompat : ∀ i j,
        M.val.map (homOfLE (show A i ⊓ A j ≤ A i from inf_le_left)).op (t i) =
          M.val.map (homOfLE (show A i ⊓ A j ≤ A j from inf_le_right)).op (t j) := by
      intro i j
      cases i with
      | none =>
        let hsub : Subsingleton Γ(M, V ⊓ A j) := hzero (V ⊓ A j) inf_le_left
        exact @Subsingleton.elim (Γ(M, V ⊓ A j)) hsub _ _
      | some x =>
        cases j with
        | none =>
          let hsub : Subsingleton Γ(M, W x ⊓ V) := hzero (W x ⊓ V) inf_le_right
          exact @Subsingleton.elim (Γ(M, W x ⊓ V)) hsub _ _
        | some y =>
          by_cases hxy : x = y
          · subst y
            rfl
          · let hsub : Subsingleton Γ(M, W x ⊓ W y) := by
              apply schemeModule_sections_subsingleton_of_support_disjoint M (W x ⊓ W y)
              intro a ha haS
              have haC := hsupport haS
              exact hxy (Subtype.ext ((hcenter x a haC ha.1).symm.trans
                (hcenter y a haC ha.2)))
            exact @Subsingleton.elim (Γ(M, W x ⊓ W y)) hsub _ _
    obtain ⟨g, hg, _⟩ := schemeModuleSections_glue M ⊤ A (fun _ => le_top) hcover t hcompat
    refine ⟨g, ?_⟩
    funext x
    change M.presheaf.germ ⊤ x.1 trivial g = z x
    have htop := M.presheaf.germ_res_apply
      (homOfLE (show W x ≤ ⊤ from le_top)) x.1 (hxW x) g
    have hrestrict : M.presheaf.map
        (homOfLE (show W x ≤ ⊤ from le_top)).op g =
          M.val.map (homOfLE (show W x ≤ U x from inf_le_left)).op (s x) :=
      hg (some x)
    rw [← htop, hrestrict]
    exact (M.presheaf.germ_res_apply
      (homOfLE (show W x ≤ U x from inf_le_left)) x.1 (hxW x) (s x)).trans (hs x)

/-- The decomposition is constructed from the actual original germ map
and its proved bijectivity, retaining the SAME original K-scalars. -/
def schemeModuleOriginalBaseTopGermsLinearEquiv
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X)
    (hC : C.Finite) (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupport : schemeModuleStalkSupport M ⊆ C) :
    SchemeModuleOpenSectionsOver pi M ⊤ ≃ₗ[K]
      (∀ x : C, SchemeModuleStalkOver pi M x.1) :=
  LinearEquiv.ofBijective (schemeModuleOriginalBaseTopGermsLinearMap pi M C)
    (schemeModuleOriginalBaseTopGermsLinearMap_bijective pi M C hC hclosed hsupport)

/-- The actual original-K global section dimension is the weighted sum
of native stalk lengths. The generic local finite-length hypotheses are
discharged by the existing actual nonzero-section quotient caller; no
decomposition or global finite-dimension premise occurs here. -/
theorem schemeModuleOriginalBaseTopSections_finite_and_weighted_finrank
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (M : X.Modules) (C : Set X)
    (hC : C.Finite) (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupport : schemeModuleStalkSupport M ⊆ C)
    (hlength : ∀ x : C, IsFiniteLength (X.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor X x.1).obj M)) :
    letI : Fintype C := hC.fintype
    Module.Finite K (SchemeModuleOpenSectionsOver pi M ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) =
        ∑ x : C, (Module.length (X.presheaf.stalk x.1)
          ((schemeModuleStalkModuleFunctor X x.1).obj M)).toNat * pi.residueDegree x.1 := by
  classical
  letI : Fintype C := hC.fintype
  have hlocal (x : C) := schemeModuleOriginalBaseStalk_finite_and_finrank
    pi M (show closedPoints X from ⟨x.1, hclosed x.1 x.2⟩) (hlength x)
  letI : ∀ x : C, Module.Finite K (SchemeModuleStalkOver pi M x.1) :=
    fun x => (hlocal x).1
  letI : Module.Finite K (∀ x : C, SchemeModuleStalkOver pi M x.1) := inferInstance
  let e := schemeModuleOriginalBaseTopGermsLinearEquiv pi M C hC hclosed hsupport
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  exact (hlocal x).2

end PfaffianDescent.Coray
