import PfaffianDescent.CorayTildeActualStalkSupport
import Mathlib.Topology.Sheaves.Stalks

/-! Actual support vanishing implies actual section vanishing, by sheaf
stalk extensionality. No section-zero or stalk-comparison certificate.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual sections on U are a subsingleton if no actual nonzero stalk
of M lies on U. This is derived from the actual sheaf germ criterion. -/
theorem schemeModule_sections_subsingleton_of_support_disjoint
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U → x ∉ schemeModuleStalkSupport M) :
    Subsingleton Γ(M, U) := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  constructor
  intro s t
  apply TopCat.Presheaf.section_ext F U s t
  intro x hx
  letI : Subsingleton (M.presheaf.stalk x) :=
    not_nontrivial_iff_subsingleton.mp (hU x hx)
  exact Subsingleton.elim _ _

/-- Every actual section on an open disjoint from actual nonzero stalks
is zero, with no local-zero certificate assumed. -/
theorem schemeModule_section_eq_zero_of_support_disjoint
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U → x ∉ schemeModuleStalkSupport M) (s : Γ(M, U)) :
    s = 0 := by
  letI : Subsingleton Γ(M, U) :=
    schemeModule_sections_subsingleton_of_support_disjoint M U hU
  exact Subsingleton.elim _ _

/-- An actual module sheaf with empty actual stalk support has only zero
sections on every original open, including original global sections. -/
theorem schemeModule_sections_subsingleton_of_support_empty
    {X : Scheme.{u}} (M : X.Modules)
    (hM : schemeModuleStalkSupport M = ∅) (U : X.Opens) :
    Subsingleton Γ(M, U) := by
  apply schemeModule_sections_subsingleton_of_support_disjoint M U
  intro x hx hsupport
  rw [hM] at hsupport
  exact hsupport

end PfaffianDescent.Coray
