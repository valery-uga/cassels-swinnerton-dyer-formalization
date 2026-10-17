import PfaffianDescent.VoisinCubicConstantFunctions
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! # The literal one-dimensional structure-sheaf section space

The already proved constancy of regular functions gives the actual
ground-field linear equivalence for morphism-valued unit sections.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- The actual ground-field scalar as a morphism-valued unit section. -/
def schemeModuleUnitGlobalSectionsScalarMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) :
    K →ₗ[K] SchemeModuleGlobalSectionsOver base (schemeModuleUnit X) where
  toFun := schemeModuleConstantEndomorphism base
  map_add' a b := (schemeModuleConstantEndomorphismAddHom base).map_add a b
  map_smul' a b := by
    change schemeModuleConstantEndomorphism base (a * b) =
      schemeModuleConstantEndomorphism base a ≫ schemeModuleConstantEndomorphism base b
    simp only [schemeModuleConstantEndomorphism, map_mul,
      unitEndomorphismOfRegularFunction_mul]

namespace ProjectiveNegativeTwist
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The literal structure-sheaf sections of a nonzero smooth cubic are
linearly equivalent to its ground field, with the original scalar map. -/
def cubicSurfaceUnitGlobalSectionsLinearEquiv
    (K : Type u) [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules] :
    K ≃ₗ[K] SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (schemeModuleUnit (hypersurface p hp)) := by
  let X := hypersurface p hp
  let base := hypersurfaceToBase p hp
  letI : Nonempty X := nonempty_hypersurface_of_nonzero_homogeneous_cubic_equation
    (by decide : 2 ≤ (4 : ℕ)) p hp hp0
  letI : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩
  letI : HasExt.{u} (SheafOfModules.{u}
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).ringCatSheaf) :=
    ‹HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules›
  have hsurj : Function.Surjective (affineFunctionHom base) :=
    p3_smoothCubicGlobalFunctions_surjective K p hp hp0
  let F := schemeModuleUnitGlobalSectionsScalarMap base
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · intro a b hab
    apply (affineFunctionHom base).injective
    have h := congrArg (unitEndomorphismValue (X := X)) hab
    change unitEndomorphismValue
        (unitEndomorphismOfRegularFunction (affineFunctionHom base a)) =
      unitEndomorphismValue
        (unitEndomorphismOfRegularFunction (affineFunctionHom base b)) at h
    simpa only [unitEndomorphismValue_ofRegularFunction] using h
  · intro s
    obtain ⟨a, ha⟩ := hsurj (unitEndomorphismValue (X := X) s)
    refine ⟨a, ?_⟩
    change unitEndomorphismOfRegularFunction (affineFunctionHom base a) = s
    rw [ha]
    exact unitEndomorphismOfRegularFunction_value s

/-- This is the actual constant-section dimension used in the Serre
extension's global section count. -/
theorem cubicSurfaceUnitGlobalSections_finrank
    (K : Type u) [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules] :
    Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (schemeModuleUnit (hypersurface p hp))) = 1 := by
  rw [← (cubicSurfaceUnitGlobalSectionsLinearEquiv K p hp hp0).finrank_eq]
  exact Module.finrank_self K

end ProjectiveNegativeTwist
end PfaffianDescent
