import PfaffianDescent.CubicCanonicalPointFieldTraceEvaluation

/-! # The exact nonvanishing obligation for canonical point trace normalization

The zero criterion is unconditional. The normalized coordinate equivalence below
explicitly requires nonvanishing of the constructed geometric coefficient.
No theorem in this file supplies that remaining global nonvanishing proof.
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
/-- The coefficient vanishes exactly when the actual global point pullback
trace vanishes. Nonzero local point Ext alone does not settle this criterion. -/
theorem cubicCanonicalPointResidueTraceCoefficient_eq_zero_iff
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))] :
    cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi = 0 ↔
      cubicCanonicalPointTraceAddHom K p hp hp0 i = 0 := by
  constructor
  · intro hc
    apply AddMonoidHom.ext
    intro z
    change cubicCanonicalPointTraceAddHom K p hp hp0 i z = 0
    rw [cubicCanonicalPointTrace_eq_fieldTrace_coordinate K p hp hp0 i hi z,
      hc, zero_mul, map_zero]
  · intro ht
    have hlinear : cubicCanonicalPointResidueTraceLinearMap K p hp hp0 i hi = 0 := by
      apply LinearMap.ext
      intro a
      change cubicCanonicalPointResidueTraceAddHom K p hp hp0 i a = 0
      change cubicCanonicalPointTraceAddHom K p hp hp0 i
        ((@cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed
          hExt hExtStalk).symm a) = 0
      rw [ht]
      rfl
    change (QuarticNet.traceDualEquiv (K := K) (L := L)).symm
      (cubicCanonicalPointResidueTraceLinearMap K p hp hp0 i hi) = 0
    rw [hlinear, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Once the actual trace coefficient is proved nonzero, multiplication by it
normalizes the constructed point Ext coordinate to the finite-field trace. -/
def cubicCanonicalPointTraceNormalizedCoordinate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (hc : cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi ≠ 0) :
    Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2 ≃+ L :=
  (@cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed hExt hExtStalk).trans
    (LinearEquiv.smulOfNeZero L L
      (cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi) hc).toAddEquiv

set_option backward.isDefEq.respectTransparency false in
theorem cubicCanonicalPointTraceNormalizedCoordinate_apply
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (hc : cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi ≠ 0)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicCanonicalPointTraceNormalizedCoordinate K p hp hp0 i hi hc z =
      cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi *
        @cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed
          hExt hExtStalk z := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The normalized coordinate evaluates the actual point pullback trace. This
identity requires exactly the explicitly stated nonzero coefficient proof. -/
theorem cubicCanonicalPointTrace_eq_fieldTrace_normalizedCoordinate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (hc : cubicCanonicalPointResidueTraceCoefficient K p hp hp0 i hi ≠ 0)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicCanonicalPointTraceAddHom K p hp hp0 i z =
      Algebra.trace K L (cubicCanonicalPointTraceNormalizedCoordinate K p hp hp0 i hi hc z) := by
  rw [cubicCanonicalPointTraceNormalizedCoordinate_apply]
  exact cubicCanonicalPointTrace_eq_fieldTrace_coordinate K p hp hp0 i hi z

end PfaffianDescent.ProjectiveNegativeTwist
