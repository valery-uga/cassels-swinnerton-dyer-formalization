import PfaffianDescent.CubicClosedPointExtKernelExistence
import PfaffianDescent.ClosedImmersionPositiveTwistExtKernel
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-! # The actual Serre extension at a closed cubic point of degree eleven

The original point residue supplies a nonzero negative-three augmentation
kernel. Intrinsic twist transport and the exact ideal sequence construct an
actual extension whose connecting class is nonzero. Local freeness is a
separate conclusion, not an input to this construction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- A degree-eleven closed field point gives a nonzero actual extension
class, with nonzero actual connecting product. -/
theorem cubicClosedPointSerreExtension_exists_nonzeroExtOne
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
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
    ∃ x : Ext.{u} (C := (hypersurface p hp).Modules)
        (closedImmersionIdealTwist i
          (positiveSheafOfModules (grading (equationIdeal p hp)) 3))
        (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 1,
      x ≠ 0 ∧
        (closedImmersionIdealTwistSequence_shortExact i
          (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp x
          (show 1 + 1 = 2 by omega) ≠ 0 := by
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
  obtain ⟨z, hz, hkernel⟩ :=
    cubicClosedPointExtKernel_exists_nonzero K p hp hp0 i hi hL
  exact @quotientPositiveTwist_exists_nonzeroExtOne_of_untwisted_kernel K _ (Fin 4) _
    (equationIdeal p hp) (Spec (.of L)) i hClosed 3 hExt z hz hkernel

set_option backward.isDefEq.respectTransparency false in
/-- The degree-eleven point determines an actual short exact Serre
extension with nonzero connecting class. No locally-free sheaf is assumed. -/
theorem cubicClosedPointSerreExtension_exists_sequence
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
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
    ∃ e : SerreExtensionSequenceData (hypersurface p hp)
        (closedImmersionIdealTwist i
          (positiveSheafOfModules (grading (equationIdeal p hp)) 3)),
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp)
          (closedImmersionIdealTwist i
            (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) e hExt)
        (show 1 + 1 = 2 by omega) ≠ 0 := by
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
  letI : HasExt.{u} (SheafOfModules.{u} (hypersurface p hp).ringCatSheaf) := hExt
  obtain ⟨x, _hx, hconnecting⟩ :=
    cubicClosedPointSerreExtension_exists_nonzeroExtOne K p hp hp0 i hi hL
  let e := SerreExtensionSequenceData.ofExtensionClass_on_scheme x
  refine ⟨e, ?_⟩
  change (closedImmersionIdealTwistSequence_shortExact i
    (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
    (SerreExtensionSequenceData.ofExtensionClass_on_scheme x).extensionClass
    (show 1 + 1 = 2 by omega) ≠ 0
  rw [SerreExtensionSequenceData.extensionClass_ofExtensionClass_on_scheme]
  exact hconnecting

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness supplies the homogeneous-coordinate domain property; no
separate domain hypothesis is needed for the actual degree-eleven extension. -/
theorem cubicClosedPointSerreExtension_exists_sequence_of_smooth
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (hL : Module.finrank K L = 11) :
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
    ∃ e : SerreExtensionSequenceData (hypersurface p hp)
        (closedImmersionIdealTwist i
          (positiveSheafOfModules (grading (equationIdeal p hp)) 3)),
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp)
          (closedImmersionIdealTwist i
            (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) e hExt)
        (show 1 + 1 = 2 by omega) ≠ 0 := by
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
  have hprime : (equationIdeal p hp).toIdeal.IsPrime := by
    change (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime
    exact principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) :=
    (Ideal.Quotient.isDomain_iff_prime (equationIdeal p hp).toIdeal).mpr hprime
  exact cubicClosedPointSerreExtension_exists_sequence K p hp hp0 i hi hL

end PfaffianDescent.ProjectiveNegativeTwist
