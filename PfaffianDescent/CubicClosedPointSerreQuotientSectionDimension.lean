import PfaffianDescent.CubicClosedPointSerreQuotientSectionExistence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The actual eight-dimensional lower bound for cubic ideal sections

This retains the full kernel dimension, rather than just choosing a nonzero
section. It is the section-count input for imposing three rank-two fibers.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Left exactness of morphism-valued global sections as an actual linear
equivalence with the kernel of the original quotient map. -/
def schemeModuleGlobalSectionsKernelEquiv
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    SchemeModuleGlobalSectionsOver base S.X₁ ≃ₗ[K]
      (schemeModuleGlobalSectionsMap base S.g).ker := by
  let F := schemeModuleGlobalSectionsMap base S.g
  let G := schemeModuleGlobalSectionsMap base S.f
  let H : SchemeModuleGlobalSectionsOver base S.X₁ →ₗ[K] F.ker :=
    LinearMap.codRestrict F.ker G (fun s => by
      apply LinearMap.mem_ker.mpr
      change (s ≫ S.f) ≫ S.g = 0
      rw [Category.assoc, S.zero, comp_zero])
  letI : Mono S.f := hS.mono_f
  refine LinearEquiv.ofBijective H ⟨?_, ?_⟩
  · intro s t h
    apply (cancel_mono S.f).mp
    exact congrArg Subtype.val h
  · intro s
    have hs : s.val ≫ S.g = 0 := LinearMap.mem_ker.mp s.property
    let t : schemeModuleUnit X ⟶ S.X₁ := hS.fIsKernel.lift (KernelFork.ofι s.val hs)
    refine ⟨t, Subtype.ext ?_⟩
    exact hS.fIsKernel.fac (KernelFork.ofι s.val hs) WalkingParallelPair.zero

namespace ProjectiveNegativeTwist
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- At an actual degree-eleven field point, the original cubic ideal has
at least eight global sections. This does not assume generic evaluation
rank or a supplied section-space comparison. -/
theorem cubicClosedPointSerreQuotientSection_finrank_ge_eight
    (K : Type u) [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    (hL : Module.finrank K L = 11) :
    8 ≤ Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3))) := by
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
  have hrange : Module.finrank K F.range ≤ 11 := by
    exact (Submodule.finrank_le F.range).trans_eq htarget
  have hdim := F.finrank_range_add_finrank_ker
  rw [hsource] at hdim
  have hkernel : 8 ≤ Module.finrank K F.ker := by omega
  have hS : S.ShortExact :=
    quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact I i 3
  let e := schemeModuleGlobalSectionsKernelEquiv base S hS
  change 8 ≤ Module.finrank K (SchemeModuleGlobalSectionsOver base S.X₁)
  rw [e.finrank_eq]
  exact hkernel

end ProjectiveNegativeTwist
end PfaffianDescent
