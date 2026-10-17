import PfaffianDescent.CubicPointTraceFieldBaseChangeAffineEndomorphism
import PfaffianDescent.CubicPointTraceFieldBaseChangeExtendedSupportScalar

/-! # The actual diagonal projector as a finite sum of geometric scalars -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PfaffianDescent.BundleSectionZeroLocus
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The constructed actual diagonal component projector is multiplication
by its actual affine regular function. -/
theorem cubicPointTraceFieldBaseChangeDiagonalSheafProjector_eq_regularFunction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    cubicPointTraceFieldBaseChangeDiagonalSheafProjector K L =
      unitEndomorphismOfRegularFunction
        (affineFunctionHom (𝟙 (Spec (.of (L ⊗[K] L))))
          (cubicPointTraceFieldBaseChangeDiagonalProjector K L)) := by
  rw [cubicPointTraceFieldBaseChangeDiagonalSheafProjector_eq_tilde,
    cubicPointTraceFieldBaseChangeAffineEndomorphism_eq_regularFunction,
    cubicPointTraceFieldBaseChangeDiagonalModuleProjector_apply, one_mul]

/-- The scalar endomorphism attached to a factor of an affine tensor ring
is the actual endomorphism defined by that factor projection. -/
theorem cubicPointTraceFieldBaseChangeAffineFactorEndomorphism
    {L R : Type u} [Field L] [CommRing R] (φ : L →+* R) (a : L) :
    unitEndomorphismOfRegularFunction
      (affineFunctionHom (𝟙 (Spec (.of R))) (φ a)) =
    schemeModuleConstantEndomorphism (Spec.map (CommRingCat.ofHom φ)) a := by
  congr 1
  have h := RingHom.congr_fun
    (affineFunctionHom_comp_Spec (𝟙 (Spec (.of R))) φ) a
  simpa only [Category.id_comp, RingHom.comp_apply] using h.symm

/-- The diagonal projector is a finite sum of actual original-point scalar
endomorphisms followed by actual new-base-field scalar endomorphisms. -/
theorem cubicPointTraceFieldBaseChangeDiagonalSheafProjector_finite_scalars
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ s : Finset (L × L),
      cubicPointTraceFieldBaseChangeDiagonalSheafProjector K L =
        ∑ ab ∈ s,
          schemeModuleConstantEndomorphism
            (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom)) ab.2 ≫
          schemeModuleConstantEndomorphism
            (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] L))) ab.1 := by
  classical
  let R := L ⊗[K] L
  let c : R →+ (SheafOfModules.unit (Spec (.of R)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of R)).ringCatSheaf) := {
    toFun := fun r => unitEndomorphismOfRegularFunction
      (affineFunctionHom (𝟙 (Spec (.of R))) r)
    map_zero' := by rw [map_zero, unitEndomorphismOfRegularFunction_zero]
    map_add' := fun r s => by rw [map_add, unitEndomorphismOfRegularFunction_add] }
  obtain ⟨s, hs⟩ := cubicPointTraceFieldBaseChangeDiagonalProjector_finite_geometric_scalars K L
  have he : cubicPointTraceFieldBaseChangeDiagonalProjector K L =
      ∑ ab ∈ s, ((1 : L) ⊗ₜ[K] ab.2) * (ab.1 ⊗ₜ[K] (1 : L)) := by
    simpa only [mul_one] using hs 1
  refine ⟨s, ?_⟩
  rw [cubicPointTraceFieldBaseChangeDiagonalSheafProjector_eq_regularFunction]
  change c (cubicPointTraceFieldBaseChangeDiagonalProjector K L) = _
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  change unitEndomorphismOfRegularFunction
    (affineFunctionHom (𝟙 (Spec (.of R)))
      (((1 : L) ⊗ₜ[K] ab.2) * (ab.1 ⊗ₜ[K] (1 : L)))) = _
  rw [map_mul, unitEndomorphismOfRegularFunction_mul]
  have hr := cubicPointTraceFieldBaseChangeAffineFactorEndomorphism
    (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom ab.2
  have hl := cubicPointTraceFieldBaseChangeAffineFactorEndomorphism
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] L) ab.1
  exact congrArg₂ (· ≫ ·) hr hl

end PfaffianDescent
