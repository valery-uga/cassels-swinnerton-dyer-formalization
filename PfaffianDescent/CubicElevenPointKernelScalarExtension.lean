import PfaffianDescent.CubicElevenPointNativeJetWitness
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridKernelScalarExtension
import PfaffianDescent.CubicKernelScalarExtensionLinearAlgebra

/-! The cubic ideal kernel over the original configuration field spans
the full eleven-point kernel over its splitting field. Full interpolation
forces the original kernel dimension; no kernel-rank certificate is used.
-/

noncomputable section
namespace PfaffianDescent

open MvPolynomial Module

universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicElevenPointValueRestriction_ker_finrank_of_surjective
    {K : Type u} [Field K] (x : Fin 11 → Fin 4 → K)
    (h : Function.Surjective (cubicElevenPointValueRestriction x)) :
    finrank K (LinearMap.ker (cubicElevenPointValueRestriction x)) = 9 := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K 3)
  have hdim := (cubicElevenPointValueRestriction x).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr h, finrank_top,
    four_variable_homogeneous_finrank, Module.finrank_pi] at hdim
  norm_num [Nat.choose] at hdim
  omega

theorem cubicElevenPoint_groundKernel_finrank_of_split_values
    {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    (R : homogeneousSubmodule (Fin 4) F 3 →ₗ[F] A)
    (hA : finrank F A ≤ 11) (x : Fin 11 → Fin 4 → E)
    (hvalues : Function.Surjective (cubicElevenPointValueRestriction x))
    (hmem : ∀ q, R q = 0 → cubicElevenPointValueRestriction x
      (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0) :
    finrank F R.ker = 9 := by
  letI : FiniteDimensional F (homogeneousSubmodule (Fin 4) F 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) F 3)
  letI : FiniteDimensional E (homogeneousSubmodule (Fin 4) E 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) E 3)
  have hsource : finrank F (homogeneousSubmodule (Fin 4) F 3) = 20 := by
    rw [four_variable_homogeneous_finrank]
    decide
  exact cubicGroundKernel_finrank_of_independent_extension R
    (cubicElevenPointValueRestriction x)
    (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E)) 11 9
    hsource hA (cubicElevenPointValueRestriction_ker_finrank_of_surjective x hvalues)
    (fun _ q hq =>
      voisinDegreeTenSelectedAvoidance_cubicFamily_linearIndependent_after_scalarExtension
        (L := E) q hq) hmem

theorem cubicElevenPoint_groundKernel_basis_spans_split_kernel
    {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    (R : homogeneousSubmodule (Fin 4) F 3 →ₗ[F] A)
    (hA : finrank F A ≤ 11) (x : Fin 11 → Fin 4 → E)
    (hvalues : Function.Surjective (cubicElevenPointValueRestriction x))
    (hmem : ∀ q, R q = 0 → cubicElevenPointValueRestriction x
      (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0)
    (B : Basis (Fin 9) F R.ker) :
    Submodule.span E (Set.range (fun i =>
      voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) (B i).1)) =
        (cubicElevenPointValueRestriction x).ker := by
  letI : FiniteDimensional E (homogeneousSubmodule (Fin 4) E 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) E 3)
  exact cubicGroundKernel_basis_spans_extended_kernel R
    (cubicElevenPointValueRestriction x)
    (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E)) 9
    (cubicElevenPointValueRestriction_ker_finrank_of_surjective x hvalues)
    (fun _ q hq =>
      voisinDegreeTenSelectedAvoidance_cubicFamily_linearIndependent_after_scalarExtension
        (L := E) q hq) hmem B

end PfaffianDescent
