import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFieldPulledSerre

/-! # The canonical section of the actual field-pulled Serre extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceFieldPulledSerre_canonicalSection
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    (serreIncidenceFieldPulledSerre (L := L) base e C).canonicalSection =
      pullbackSection (schemeFieldBaseChangeToOriginal (L := L) base)
        (show X.Modules from e.E)
        (isIso_pullbackUnitComparison (schemeFieldBaseChangeToOriginal (L := L) base))
        e.canonicalSection := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  apply ((Scheme.Modules.pullback g).obj (show X.Modules from e.E)).unitHomEquiv.symm.injective
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  simp only [SerreExtensionData.canonicalSection, ← SheafOfModules.unitHomEquiv_symm_comp,
    Equiv.symm_apply_apply, Category.id_comp]
  rfl

end PfaffianDescent
