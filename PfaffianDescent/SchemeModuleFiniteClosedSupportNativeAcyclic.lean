import PfaffianDescent.SchemeModuleFiniteClosedSupportOriginalBaseGerms
import PfaffianDescent.SheafModuleFlasque

/-! SOURCE ONLY. Actual finite closed-point stalk support implies native
flasqueness and positive-degree acyclicity. No quasicoherence, geometric
integrality, constants-field or acyclicity certificate is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Extend an actual section by its germs on the finite support, choosing
zero at the support points outside its open. Actual stalk extensionality
then proves that the constructed global section has the required restriction. -/
theorem schemeModuleFiniteClosedSupport_topRestriction_surjective
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X)
    (hC : C.Finite) (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupport : schemeModuleStalkSupport M ⊆ C) (U : X.Opens) :
    Function.Surjective (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  classical
  intro s
  let z : ∀ x : C, SchemeModuleStalkOver pi M x.1 := fun x =>
    if hx : x.1 ∈ U then M.presheaf.germ U x.1 hx s else 0
  obtain ⟨g, hg⟩ := (schemeModuleOriginalBaseTopGermsLinearMap_bijective
    pi M C hC hclosed hsupport).2 z
  refine ⟨g, ?_⟩
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  apply TopCat.Presheaf.section_ext F U
  intro x hx
  rw [M.presheaf.germ_res_apply]
  by_cases hxC : x ∈ C
  · have h := congrFun hg (⟨x, hxC⟩ : C)
    change M.presheaf.germ ⊤ x trivial g = _ at h
    simpa only [z, dif_pos hx] using h
  · have hxoff : x ∉ schemeModuleStalkSupport M := fun h => hxC (hsupport h)
    letI : Subsingleton (M.presheaf.stalk x) :=
      not_nontrivial_iff_subsingleton.mp hxoff
    exact Subsingleton.elim _ _

/-- All actual restrictions are surjective because every section extends
all the way to the top open; the additive presheaf is therefore flasque. -/
theorem schemeModuleFiniteClosedSupport_isFlasque
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X)
    (hC : C.Finite) (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupport : schemeModuleStalkSupport M ⊆ C) :
    TopCat.Presheaf.IsFlasque M.val.presheaf where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro s
    obtain ⟨g, hg⟩ := schemeModuleFiniteClosedSupport_topRestriction_surjective
      pi M C hC hclosed hsupport V.unop s
    refine ⟨M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op g, ?_⟩
    change M.val.map i
      (M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op g) = s
    rw [← M.val.map_comp_apply]
    have hi : (homOfLE (show U.unop ≤ ⊤ from le_top)).op ≫ i =
        (homOfLE (show V.unop ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
    rw [hi]
    exact hg

/-- Native positive cohomology vanishes for the SAME actual coefficient.
Enough injectives and flasqueness are derived inside this theorem. -/
theorem schemeModuleFiniteClosedSupport_cohomology_succ_subsingleton
    [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (C : Set X)
    (hC : C.Finite) (hclosed : ∀ x ∈ C, IsClosed ({x} : Set X))
    (hsupport : schemeModuleStalkSupport M ⊆ C) (a : ℕ) :
    Subsingleton (schemeModuleCohomology X M (a + 1)) := by
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : TopCat.Presheaf.IsFlasque M.val.presheaf :=
    schemeModuleFiniteClosedSupport_isFlasque pi M C hC hclosed hsupport
  exact flasque_schemeModuleCohomology_succ X M a

end PfaffianDescent.Coray
