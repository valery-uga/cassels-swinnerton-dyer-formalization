import PfaffianDescent.CubicCanonicalPointCoordinateScalar
import PfaffianDescent.CubicCanonicalPointTraceResidueCoordinate
import PfaffianDescent.CubicCanonicalPointTraceCoefficientScalar
import PfaffianDescent.AdditiveTraceCoordinateScalar

/-! # Ground-field linearity of the actual canonical point residue trace -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The constructed actual residue trace respects the ground-field scalar action.
Both coordinate and geometric trace compatibility are proved internally. -/
theorem cubicCanonicalPointResidueTrace_scalar
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (c : K) (a : L) :
    cubicCanonicalPointResidueTraceAddHom K p hp hp0 i (algebraMap K L c * a) =
      c * cubicCanonicalPointResidueTraceAddHom K p hp hp0 i a := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading (equationIdeal p hp))).ringCatSheaf) := hExt
  letI : HasExt.{u} (hypersurface p hp).Modules := hExt
  let e := @cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed
    hExt hExtStalk
  let tr := @cubicCanonicalPointTraceAddHom K _ p hp hp0 hDomain L _ i hClosed
    hExtAmbient hExt
  let phi := mulHomogeneous (grading (equationIdeal p hp))
    (cubicScalarHomogeneous K p hp c) 1
  let phiExt : Ext.{u} (sheafOfModules (grading (equationIdeal p hp)) 1)
      (sheafOfModules (grading (equationIdeal p hp)) 1) 0 :=
    Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules) phi
  change additiveTraceCoordinateAddHom e tr (algebraMap K L c * a) =
    c * additiveTraceCoordinateAddHom e tr a
  exact additiveTraceCoordinateAddHom_map_action.{u, u, u} e tr
    (fun z => z.comp phiExt (add_zero 2))
    (fun b => algebraMap K L c * b) (fun b => c * b)
    (fun z => @cubicCanonicalPointExtTwoCoordinate_postcomp_scalar
      K _ p hp hp0 hSmooth L _ _ i hClosed hi hExt hExtStalk c z)
    (fun z => @cubicCanonicalPointTraceAddHom_postcomp_scalar
      K _ p hp hp0 hDomain L _ i hClosed hExtAmbient hExt c z) a

set_option backward.isDefEq.respectTransparency false in
/-- The actual geometric residue trace as a ground-field linear map. Nonvanishing
and identification with a normalized field trace are separate obligations. -/
def cubicCanonicalPointResidueTraceLinearMap
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))] :
    L →ₗ[K] K where
  toFun := cubicCanonicalPointResidueTraceAddHom K p hp hp0 i
  map_add' := (cubicCanonicalPointResidueTraceAddHom K p hp hp0 i).map_add
  map_smul' c a := by
    change cubicCanonicalPointResidueTraceAddHom K p hp hp0 i (c • a) =
      c * cubicCanonicalPointResidueTraceAddHom K p hp hp0 i a
    exact (congrArg (cubicCanonicalPointResidueTraceAddHom K p hp hp0 i)
      (Algebra.smul_def c a)).trans
        (cubicCanonicalPointResidueTrace_scalar K p hp hp0 i hi c a)

end PfaffianDescent.ProjectiveNegativeTwist
