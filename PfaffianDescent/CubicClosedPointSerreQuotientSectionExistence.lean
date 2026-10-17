import PfaffianDescent.CubicClosedPointSerreQuotientSectionLinear
import PfaffianDescent.VoisinCubicThreeGlobalSections

/-! # A nonzero actual positive-three ideal section at a degree-eleven point

The native restriction map has a nineteen-dimensional source and an
eleven-dimensional target. Its nonzero kernel lifts through the original
short exact ideal sequence to a nonzero global section of the twisted ideal.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Every actual degree-eleven field point on a nonzero smooth cubic over
an infinite field has a nonzero global section of its positive-three ideal
twist. No section comparison or nonzero section is an input. -/
theorem cubicClosedPointSerreQuotientSection_exists_nonzero
    (K : Type u) [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    (hL : Module.finrank K L = 11) :
    ∃ t : (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).sections,
      t ≠ SerreExtensionData.zeroSection _ := by
  let I := equationIdeal p hp
  let T := positiveSheafOfModules (grading I) 3
  let S := closedImmersionIdealTwistSequence i T
  let base := hypersurfaceToBase p hp
  letI : PreservesFiniteLimits (schemeModuleTensorRight T) :=
    quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
  let eM := cubicClosedPointSerreQuotientSection_globalSectionsIso base
    (closedImmersionIdealTwistSequence_middleIso i T)
  let eC := cubicPositiveThreeGlobalSectionsLinearEquiv K p hp hp0
  letI : Module.Finite K (grading I 3) := polynomialQuotientGrade_finite I 3
  letI : FiniteDimensional K (SchemeModuleGlobalSectionsOver base S.X₂) :=
    Module.Finite.of_surjective (eC.trans eM.symm).toLinearMap
      (eC.trans eM.symm).surjective
  let eP := cubicClosedPointSerreQuotientSection_targetGlobalSectionsEquiv K p hp i hi
  letI : FiniteDimensional K (SchemeModuleGlobalSectionsOver base S.X₃) :=
    Module.Finite.of_surjective eP.symm.toLinearMap eP.symm.surjective
  have hsource : Module.finrank K (SchemeModuleGlobalSectionsOver base S.X₂) = 19 :=
    eM.finrank_eq.trans (cubicPositiveThreeGlobalSections_finrank K p hp hp0)
  have htarget : Module.finrank K (SchemeModuleGlobalSectionsOver base S.X₃) = 11 :=
    eP.finrank_eq.trans hL
  let F := schemeModuleGlobalSectionsMap base S.g
  have hker : F.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [htarget, hsource]
    decide)
  obtain ⟨s, hs, hsne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hs0 : s ≫ S.g = 0 := LinearMap.mem_ker.mp hs
  have hS : S.ShortExact :=
    quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact I i 3
  let q : schemeModuleUnit (hypersurface p hp) ⟶ S.X₁ :=
    hS.fIsKernel.lift (KernelFork.ofι s hs0)
  have hq : q ≫ S.f = s :=
    hS.fIsKernel.fac (KernelFork.ofι s hs0) WalkingParallelPair.zero
  have hqne : q ≠ 0 := by
    intro hq0
    apply hsne
    rw [← hq, hq0, zero_comp]
  refine ⟨S.X₁.unitHomEquiv q, ?_⟩
  intro ht
  apply hqne
  change S.X₁.unitHomEquiv q = SerreExtensionData.zeroSection S.X₁ at ht
  have h := congrArg S.X₁.unitHomEquiv.symm ht
  simpa only [Equiv.symm_apply_apply,
    SerreExtensionData.unitHomEquiv_symm_zeroSection] using h

end PfaffianDescent.ProjectiveNegativeTwist
