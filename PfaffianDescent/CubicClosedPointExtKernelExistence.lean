import PfaffianDescent.CubicClosedPointExtKernelLinear

/-! # A nonzero actual degree-eleven closed-point Ext kernel

The residue field has dimension eleven, whereas the actual homogeneous
quadratic dual has dimension ten. The original point restriction therefore
has a nonzero Ext kernel class. No geometric trace nonvanishing, duality
naturality square, or finite-support comparison is a premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The original unit restriction has a nonzero negative-three Ext kernel
at every actual separable closed field point of degree eleven. -/
theorem cubicClosedPointExtKernel_exists_nonzero
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (hL : Module.finrank K L = 11) :
    ∃ z : Ext.{u} (C := (hypersurface p hp).Modules)
        (closedImmersionIdealTwistSequence i
          (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
        (sheafOfModules (grading (equationIdeal p hp)) 3) 2,
      z ≠ 0 ∧
        (Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
            (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2) = 0 := by
  let F := @cubicClosedPointExtKernelMap K _ p hp hp0 hDomain hSmooth
    L _ _ _ _ i hClosed hi hExtAmbient hExt hExtStalk
  have hquad : Module.finrank K
      (Module.Dual K (MvPolynomial.homogeneousSubmodule (Fin 4) K 2)) = 10 := by
    rw [Subspace.dual_finrank_eq, four_variable_homogeneous_finrank]
    decide
  have hker : F.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [hquad, hL]
    decide)
  obtain ⟨a, ha, hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let e := @cubicPointCompatibleNegativeThreeResidueEquiv K _ p hp hp0 hSmooth
    L _ i hClosed hExt hExtStalk
  let d := @cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K _ p hp hp0
    hDomain hExtAmbient hExt
  refine ⟨e.symm a, ?_, ?_⟩
  · intro hz
    apply hane
    have h := congrArg e hz
    simpa only [AddEquiv.apply_symm_apply, map_zero] using h
  · apply d.injective
    change F a = d 0
    simpa only [map_zero] using (LinearMap.mem_ker.mp ha)

end PfaffianDescent.ProjectiveNegativeTwist
