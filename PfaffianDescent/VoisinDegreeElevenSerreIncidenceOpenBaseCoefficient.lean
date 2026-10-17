import PfaffianDescent.VoisinDegreeElevenSerreIncidenceAffineGeometricTensor
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Literal coefficient compatibility of actual affine open coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceOpenBaseCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (U : X.Opens) :
    U.topIso.hom.hom.comp (schemeOpenBaseRingHom (U.ι ≫ base) ⊤) =
      schemeOpenBaseRingHom base U := by
  ext k
  simp only [RingHom.comp_apply, schemeOpenBaseRingHom_top_apply,
    affineFunctionHom_comp, RingHom.comp_apply, Scheme.Opens.ι_appTop,
    Scheme.Opens.topIso_hom]
  change (X.presheaf.map (eqToHom _).op)
    (X.presheaf.map (homOfLE le_top).op (affineFunctionHom base k)) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem serreIncidenceGeometric_open_tensor_isDomain
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) [GeometricallyIntegral base]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty (U : Scheme.{u})] :
    letI := RingHom.toAlgebra (schemeOpenBaseRingHom base U)
    IsDomain (L ⊗[K] Γ(X, U)) := by
  letI := RingHom.toAlgebra (schemeOpenBaseRingHom base U)
  letI : IsAffine (U : Scheme.{u}) := hU
  letI := RingHom.toAlgebra (schemeOpenBaseRingHom (U.ι ≫ base) ⊤)
  letI : GeometricallyIntegral (U.ι ≫ base) := serreIncidenceGeometric_sourceOpen base U
  letI : IsDomain (L ⊗[K] Γ(U, ⊤)) :=
    serreIncidenceGeometricAffine_tensor_isDomain (L := L) (U.ι ≫ base)
  let e : Γ(U, ⊤) ≃ₐ[K] Γ(X, U) :=
    { __ := U.topIso.commRingCatIsoToRingEquiv
      commutes' := fun k => RingHom.congr_fun (serreIncidenceOpenBaseCoefficient base U) k }
  let t := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e
  exact Function.Injective.isDomain t.symm.toRingHom t.symm.injective

end PfaffianDescent
