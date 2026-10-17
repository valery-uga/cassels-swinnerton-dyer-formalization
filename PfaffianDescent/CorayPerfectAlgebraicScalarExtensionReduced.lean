import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.FiniteType

/-! Literal algebraic scalar extension of an original domain is reduced over
perfect K. No reducedness/geometric integrality premise is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open scoped TensorProduct
universe u
set_option autoImplicit false

/-- Tensoring an arbitrary K-field F with an algebraic field extension E of
perfect K is reduced. Finite type subalgebras of E give separable unramified
field tensors; native finite-support tensor descent handles the entire E. -/
theorem perfectField_algebraicField_tensor_with_field_isReduced001
    (K E F : Type u) [Field K] [PerfectField K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra.IsAlgebraic K E] :
    IsReduced (E ⊗[K] F) := by
  have hFiniteSub : ∀ B : Subalgebra K E, B.FG → IsReduced (F ⊗[K] B) := by
    intro B hB
    letI : Field B := (Subalgebra.isField_of_algebraic B).toField
    letI : Algebra.IsAlgebraic K B :=
      Algebra.IsAlgebraic.of_injective B.val Subtype.val_injective
    letI : Algebra.FiniteType K B := (Subalgebra.fg_iff_finiteType B).mp hB
    letI : Algebra.IsSeparable K B := inferInstance
    letI : Algebra.FormallyUnramified K B :=
      Algebra.FormallyUnramified.of_isSeparable K B
    letI : Algebra.FormallyUnramified F (F ⊗[K] B) := inferInstance
    letI : Algebra.EssFiniteType F (F ⊗[K] B) := inferInstance
    exact Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[K] B)
  letI : IsReduced (F ⊗[K] E) := IsReduced.tensorProduct_of_flat_of_forall_fg hFiniteSub
  exact isReduced_of_injective (Algebra.TensorProduct.comm K E F)
    (Algebra.TensorProduct.comm K E F).injective

/-- The SAME original domain A embeds into its own fraction field; flat
scalar tensor preserves that literal injection. Reducedness of the field
tensor proves reducedness of the entire original tensor, without GI. -/
theorem perfectField_algebraicField_tensor_with_domain_isReduced001
    (K E A : Type u) [Field K] [PerfectField K] [Field E]
    [CommRing A] [IsDomain A] [Algebra K E] [Algebra K A]
    [Algebra.IsAlgebraic K E] : IsReduced (E ⊗[K] A) := by
  let F := FractionRing A
  let f : A →ₐ[K] F := IsScalarTower.toAlgHom K A F
  have hf : Function.Injective f := IsFractionRing.injective A F
  letI : IsReduced (E ⊗[K] F) :=
    perfectField_algebraicField_tensor_with_field_isReduced001 K E F
  let g : E ⊗[K] A →ₐ[K] E ⊗[K] F :=
    Algebra.TensorProduct.map (AlgHom.id K E) f
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  exact isReduced_of_injective g hg

end PfaffianDescent.Coray
