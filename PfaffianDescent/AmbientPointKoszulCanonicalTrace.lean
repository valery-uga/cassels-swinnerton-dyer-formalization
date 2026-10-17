import PfaffianDescent.AmbientPointKoszulResolution
import PfaffianDescent.PointGlobalTraceP3ResolutionTrace

/-! # The actual canonical trace of the standard ambient point

The geometric point resolution, all six twist Ext vanishings and the
ambient canonical trace are now constructed internally. No geometric
resolution or trace nonvanishing premise is supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The actual standard-point augmentation followed by the canonical
ambient trace is an additive equivalence. -/
def ambientPointKoszul_canonicalTraceEquiv
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Ext.{u} (C := (Proj PS).Modules)
      (ambientPointKoszul_pointModule K) (sheafOfModules PS 4) 3 ≃+ K :=
  pointGlobalTraceP3ResolutionTraceEquiv K (ambientPointKoszul_resolution K)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- This equivalence uses the original closed-immersion restriction and
the already constructed native projective canonical trace. -/
theorem ambientPointKoszul_canonicalTraceEquiv_apply
    [hExt : HasExt.{u} (Proj PS).Modules]
    (z : Ext.{u} (C := (Proj PS).Modules)
      (ambientPointKoszul_pointModule K) (sheafOfModules PS 4) 3) :
    ambientPointKoszul_canonicalTraceEquiv K z =
      p3NegativeFourCohomologyThreeTraceEquiv K
        ((Ext.mk₀.{u} (C := (Proj PS).Modules)
          (ambientPointKoszul_augmentation K)).comp z (zero_add 3)) := by
  change pointGlobalTraceP3ResolutionTraceEquiv K
    (ambientPointKoszul_resolution K) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) z = _
  rw [pointGlobalTraceP3ResolutionTraceEquiv_apply]
  rfl

/-- Pullback along the actual standard-point augmentation is injective
in ambient canonical Ext degree three. -/
theorem ambientPointKoszul_augmentation_precomp_injective
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Function.Injective
      ((Ext.mk₀.{u} (C := (Proj PS).Modules)
        (ambientPointKoszul_augmentation K)).precomp (sheafOfModules PS 4) (zero_add 3)) := by
  intro z w h
  apply (ambientPointKoszul_canonicalTraceEquiv K).injective
  rw [ambientPointKoszul_canonicalTraceEquiv_apply,
    ambientPointKoszul_canonicalTraceEquiv_apply]
  exact congrArg (p3NegativeFourCohomologyThreeTraceEquiv K) h

/-- There is an actual point Ext class with canonical augmentation trace one. -/
theorem ambientPointKoszul_exists_canonical_trace_one
    [hExt : HasExt.{u} (Proj PS).Modules] :
    ∃ z : Ext.{u} (C := (Proj PS).Modules)
        (ambientPointKoszul_pointModule K) (sheafOfModules PS 4) 3,
      p3NegativeFourCohomologyThreeTraceEquiv K
        ((Ext.mk₀.{u} (C := (Proj PS).Modules)
          (ambientPointKoszul_augmentation K)).comp z (zero_add 3)) = 1 := by
  refine ⟨(ambientPointKoszul_canonicalTraceEquiv K).symm 1, ?_⟩
  rw [← ambientPointKoszul_canonicalTraceEquiv_apply]
  exact (ambientPointKoszul_canonicalTraceEquiv K).apply_symm_apply 1

end PfaffianDescent.ProjectiveNegativeTwist
