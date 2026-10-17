import PfaffianDescent.CubicRationalPointAmbientAugmentationInjective

/-! # The actual rational cubic point trace detects a nonzero Cartier boundary

Ambient augmentation injectivity is proved by the actual centered-point
resolution and canonical unit comparisons. Only the original nonzero
Cartier boundary remains as an input to the native trace criterion.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- For an actual rational cubic-surface point, the original canonical
trace is nonzero whenever the original actual Cartier boundary is nonzero.
There is no ambient augmentation comparison or injectivity premise. -/
theorem cubicRationalPointAmbientAugmentation_trace_ne_zero_of_boundary
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    (i : Spec (.of K) ⟶ Proj (grading (equationIdeal p hp))) [IsClosedImmersion i]
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExtSurface : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (hi : i ≫ hypersurfaceToBase p hp = 𝟙 (Spec (.of K)))
    (z : Ext.{u} (C := (Proj (grading (equationIdeal p hp))).Modules)
      (closedImmersionIdealTwistSequence i
        (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2)
    (hboundary :
      letI : HasExt.{u} (hypersurface p hp).Modules := hExtSurface
      letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExtAmbient
      (z.mapExactFunctor (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))).comp
        (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass rfl ≠ 0) :
    cubicCanonicalPointTraceAddHom K p hp hp0 i z ≠ 0 :=
  cubicPointCartier_trace_ne_zero_of_ambient_boundary K p hp hp0 i z
    (cubicRationalPointAmbientAugmentation_precomp_injective K p hp i hi) hboundary

end PfaffianDescent.ProjectiveNegativeTwist
