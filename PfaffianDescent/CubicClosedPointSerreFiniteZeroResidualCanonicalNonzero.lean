import PfaffianDescent.SerreExtensionFoundation

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_canonicalSection_nonzero
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (x : X) : e.canonicalSection ≠ SerreExtensionData.zeroSection e.E := by
  let O := SheafOfModules.unit X.ringCatSheaf
  letI : Nontrivial Γ(X, ⊤) := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  apply e.inclusion_sections_ne_zero_of_ne_zero
  intro hz
  change O.unitHomEquiv (𝟙 O) = SerreExtensionData.zeroSection O at hz
  have hid : (𝟙 O : O ⟶ O) = 0 := by
    have h := congrArg O.unitHomEquiv.symm hz
    simpa only [Equiv.symm_apply_apply, SerreExtensionData.unitHomEquiv_symm_zeroSection] using h
  have h1 := congrArg (fun f : O ⟶ O => f.val.app (op ⊤) (1 : Γ(X, ⊤))) hid
  change (1 : Γ(X, ⊤)) = 0 at h1
  exact one_ne_zero h1

/-- The literal morphism-valued global section used by the native projective
parameter construction is nonzero on every nonempty actual surface. -/
theorem cubicClosedPointSerreFiniteZeroResidual_canonicalGlobalSection_nonzero
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (x : X) : e.inclusion ≠ 0 := by
  intro hi
  apply cubicClosedPointSerreFiniteZeroResidual_canonicalSection_nonzero e x
  unfold SerreExtensionData.canonicalSection
  rw [← SheafOfModules.unitHomEquiv_comp_apply, Category.id_comp, hi]
  rfl

end PfaffianDescent
