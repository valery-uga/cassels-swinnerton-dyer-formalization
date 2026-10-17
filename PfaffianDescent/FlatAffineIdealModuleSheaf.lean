import PfaffianDescent.FlatIdealBaseChangeNaturality
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! The flat affine quotient-kernel comparison as an isomorphism of sheaves. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

/-- On the affine scheme after flat base change, the `tilde` sheaf of
the scalar-extended ideal is isomorphic to the `tilde` sheaf of the
actual quotient-kernel ideal. -/
noncomputable def flatBaseChangeQuotientKernelTildeIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (B ⊗[A] I)) ≅
    (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B
        (RingHom.ker (Algebra.TensorProduct.includeLeft
          (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom)) := by
  letI : Algebra A B := g.toAlgebra
  let e := flatBaseChangeQuotientKernelLinearEquiv g hg I
  let m := ModuleCat.ofHom e.toLinearMap
  haveI : IsIso m :=
    (ConcreteCategory.isIso_iff_bijective m).mpr e.bijective
  exact (tilde.functor (CommRingCat.of B)).mapIso (asIso m)

end PfaffianDescent
