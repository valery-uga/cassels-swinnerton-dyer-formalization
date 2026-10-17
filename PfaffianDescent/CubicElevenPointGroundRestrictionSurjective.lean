import PfaffianDescent.CubicElevenPointKernelScalarExtension

/-! The actual degree-eleven cubic restriction is onto once full
interpolation has established its nine-dimensional polynomial kernel. -/

noncomputable section
namespace PfaffianDescent

open MvPolynomial Module

universe u

theorem cubicElevenPoint_groundRestriction_surjective
    {F A : Type u} [Field F] [AddCommGroup A] [Module F A]
    [FiniteDimensional F A]
    (R : homogeneousSubmodule (Fin 4) F 3 →ₗ[F] A)
    (hA : finrank F A = 11) (hker : finrank F R.ker = 9) :
    Function.Surjective R := by
  letI : FiniteDimensional F (homogeneousSubmodule (Fin 4) F 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) F 3)
  have hsource : finrank F (homogeneousSubmodule (Fin 4) F 3) = 20 := by
    rw [four_variable_homogeneous_finrank]
    decide
  have hdim := R.finrank_range_add_finrank_ker
  rw [hsource, hker] at hdim
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  omega

end PfaffianDescent
