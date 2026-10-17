import Mathlib.LinearAlgebra.Dual.Lemmas
import PfaffianDescent.VoisinCubicPositiveGlobalSections

/-!
# Selecting the dual kernel functional in Voisin's Serre construction

Failure of quadratic interpolation on the length-eleven subscheme produces
a nonzero linear functional on its quadratic sections that kills every
restricted global quadratic.  This is the finite-dimensional linear-algebra
half of the specific Serre-duality calculation.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

namespace PfaffianDescent

/-- A nonsurjective linear map admits a nonzero functional on its target
which vanishes on its range.  Equivalently, the dual map has a nonzero
kernel element. -/
theorem exists_nonzero_dualMap_kernel_of_not_surjective
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : ¬ Function.Surjective f) :
    ∃ phi : Module.Dual K W, phi ≠ 0 ∧ f.dualMap phi = 0 := by
  rw [← LinearMap.range_eq_top, ← Ne, ← lt_top_iff_ne_top] at hf
  obtain ⟨phi, hphi, hrange⟩ := (LinearMap.range f).exists_le_ker_of_lt_top hf
  refine ⟨phi, hphi, ?_⟩
  apply LinearMap.ext
  intro v
  simpa [LinearMap.dualMap_apply] using hrange ⟨v, rfl⟩

namespace ProjectiveNegativeTwist

/-- A length-eleven finite subscheme of a cubic surface has a nonzero
functional on its coefficient algebra which annihilates every restricted
quadratic section.

This is the concrete dual-kernel class underlying the Serre-duality step;
the remaining geometric comparison identifies this functional with the
corresponding kernel element in global `Ext²`. -/
theorem cubic_length_eleven_exists_nonzero_positiveTwoRestriction_dual_kernel
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (equationIdeal p hp))
    [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))]
    (hlen : finiteSchemeRank (i ≫ toBase (equationIdeal p hp)) = 11) :
    letI := finiteSchemeCoefficientAlgebra
      (i ≫ toBase (equationIdeal p hp))
    ∃ phi : Module.Dual K Γ(Z, ⊤), phi ≠ 0 ∧
      (finiteProjectiveClosedSubschemePositiveTwoRestrictionLinearMap
        (equationIdeal p hp) i).dualMap phi = 0 := by
  letI := finiteSchemeCoefficientAlgebra
    (i ≫ toBase (equationIdeal p hp))
  apply exists_nonzero_dualMap_kernel_of_not_surjective
  exact cubic_length_eleven_positiveTwoRestriction_not_surjective
    p hp hp0 i hlen

end ProjectiveNegativeTwist
end PfaffianDescent
