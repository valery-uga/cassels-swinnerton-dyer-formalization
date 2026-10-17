import PfaffianDescent.CubicCanonicalPointResidueTraceLinear
import PfaffianDescent.QuarticTraceDuality

/-! # Field-trace coefficient of the actual canonical point trace

The actual geometric trace is represented by the separable field trace. Its
coefficient is not asserted to be nonzero; proving that is the remaining global
nonvanishing obligation needed for a normalized coordinate equivalence.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The unique field-trace coefficient representing the actual canonical residue trace. -/
def cubicCanonicalPointResidueTraceCoefficient
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))] : L :=
  (QuarticNet.traceDualEquiv (K := K) (L := L)).symm
    (cubicCanonicalPointResidueTraceLinearMap K p hp hp0 i hi)

set_option backward.isDefEq.respectTransparency false in
/-- Actual geometric residue trace equals the field trace after multiplication by
its constructed coefficient, with no trace-normalization premise. -/
theorem cubicCanonicalPointResidueTrace_eq_fieldTrace
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))] (a : L) :
    cubicCanonicalPointResidueTraceAddHom K p hp hp0 i a =
      Algebra.trace K L (cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi * a) := by
  have h := (QuarticNet.traceDualEquiv (K := K) (L := L)).apply_symm_apply
    (cubicCanonicalPointResidueTraceLinearMap K p hp hp0 i hi)
  have he := congrArg (fun f : Module.Dual K L => f a) h
  exact he.symm.trans (QuarticNet.traceDualEquiv_apply _ _)

end PfaffianDescent.ProjectiveNegativeTwist
