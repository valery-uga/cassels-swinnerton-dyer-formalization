import PfaffianDescent.CubicClosedPointSerreQuotientSectionExistence
import PfaffianDescent.VoisinCubicSurfaceSerre

/-! # A native Serre pencil seed from the actual closed-point quotient

Once the actual Serre extension's local freeness has been established, the
nonzero ideal section constructed from the literal point restriction gives
the two-section seed. No quotient section remains an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- The actual positive-three Serre extension at a degree-eleven field
point admits its native pencil seed without a supplied quotient section. -/
theorem cubicClosedPointSerreQuotientSection_nonempty_pencilSeed
    (K : Type u) [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules]
    (hL : Module.finrank K L = 11)
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3))) :
    Nonempty (SerreExtensionData.SerreExtensionPencilSeed e) := by
  obtain ⟨t, ht⟩ :=
    cubicClosedPointSerreQuotientSection_exists_nonzero K p hp hp0 i hi hL
  exact nonempty_serreExtensionPencilSeed_of_smooth_cubicSurface K p hp hp0 e t ht

end PfaffianDescent.ProjectiveNegativeTwist
