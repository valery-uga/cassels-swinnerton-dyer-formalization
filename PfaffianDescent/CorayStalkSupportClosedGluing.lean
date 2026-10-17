import PfaffianDescent.CorayActualStalkSupportTransport

/-! Closedness of actual module-sheaf stalk support glues over open immersions.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- Closedness of ACTUAL nonzero-stalk support is local for an ACTUAL open
immersion cover. No finiteness of the index or comparison certificate is needed. -/
theorem schemeModuleStalkSupport_isClosed_of_open_cover
    {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, ∃ y : Y i, f i y = x)
    (hclosed : ∀ i, IsClosed (schemeModuleStalkSupport
      ((Scheme.Modules.restrictFunctor (f i)).obj M))) :
    IsClosed (schemeModuleStalkSupport M) := by
  have heq : (schemeModuleStalkSupport M)ᶜ =
      ⋃ i, (f i) '' (schemeModuleStalkSupport
        ((Scheme.Modules.restrictFunctor (f i)).obj M))ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, y, hy⟩ := hcover x
      apply Set.mem_iUnion.mpr
      refine ⟨i, y, ?_, hy⟩
      rw [schemeModuleStalkSupport_restrict]
      change f i y ∉ schemeModuleStalkSupport M
      simpa only [Set.mem_compl_iff, hy] using hx
    · intro hx
      obtain ⟨i, y, hy, hyx⟩ := Set.mem_iUnion.mp hx
      rw [schemeModuleStalkSupport_restrict] at hy
      change f i y ∉ schemeModuleStalkSupport M at hy
      simpa only [Set.mem_compl_iff, hyx] using hy
  apply isOpen_compl_iff.mp
  rw [heq]
  exact isOpen_iUnion fun i =>
    (f i).isOpenEmbedding.isOpenMap _ (hclosed i).isOpen_compl

end PfaffianDescent.Coray
