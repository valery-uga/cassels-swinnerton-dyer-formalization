import PfaffianDescent.CubicIntrinsicCanonicalTraceGroundLinear

/-! Original-K linearity of the SAME selected-component residue trace.
No duality/perfectness/genus assertion. SOURCE ONLY / UNVERIFIED.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MvPolynomial TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Abstract projection adapter: keep all native carrier/dictionary data as parameters. -/
private theorem nativeLinearEquivAdditiveProjection
    {V : Type u} [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] K) (a : V ≃+ K) (h : e.toAddEquiv = a) :
    e.toLinearMap.toAddMonoidHom = a.toAddMonoidHom := by
  exact (LinearEquiv.toAddMonoidHom_commutes e).trans
    (congrArg (fun b : V ≃+ K => b.toAddMonoidHom) h)

/-- Abstract map equality adapter, without a concrete cohomology carrier lambda. -/
private theorem nativeLinearMapAdditiveTransport
    {V : Type u} [AddCommGroup V] [Module K V]
    {f g : V →ₗ[K] K} (h : f = g) :
    f.toAddMonoidHom = g.toAddMonoidHom :=
  congrArg (fun a : V →ₗ[K] K => a.toAddMonoidHom) h

/-- Isolate the actual canonical coefficient/action projection before any immersion. -/
def cubicNativeCanonicalTraceLinearMap
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := hExt
    letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    schemeModuleCohomology X W 2 →ₗ[K] K := by
  let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
  let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : HasExt.{u} X.Modules := hExt
  letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
  letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
  letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
  let tau := @cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv K
    (inferInstance : Field K) p hp hp0
    (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
    ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt
  exact tau.toLinearMap

/-- First endpoint cut: SAME typed native producer, before the additive trace RHS. -/
private theorem cubicNativeCanonicalTraceLinearMap_eq_projection
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := hExt
    letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    cubicNativeCanonicalTraceLinearMap p hp hp0 =
      (cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv K p hp hp0).toLinearMap := by
  rfl

/-- Isolate ONLY the original native producer-to-projection additive conversion. -/
theorem cubicNativeCanonicalTraceLinearMap_projection_toAddMonoidHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := hExt
    letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    (cubicNativeCanonicalTraceLinearMap p hp hp0).toAddMonoidHom =
      (cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv K p hp hp0).toLinearMap.toAddMonoidHom := by
  let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
  let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : HasExt.{u} X.Modules := hExt
  letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
  let nativeGroup : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
  letI : AddCommGroup (schemeModuleCohomology X W 2) := nativeGroup
  let nativeModule : Module K (schemeModuleCohomology X W 2) := Ext.instModule
  letI : Module K (schemeModuleCohomology X W 2) := nativeModule
  have hProjection := @cubicNativeCanonicalTraceLinearMap_eq_projection K
    (inferInstance : Field K) p hp hp0
    (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
    ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt
  exact @nativeLinearMapAdditiveTransport K (inferInstance : Field K)
    (schemeModuleCohomology X W 2) nativeGroup nativeModule
    (cubicNativeCanonicalTraceLinearMap p hp hp0)
    (cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv K p hp hp0).toLinearMap
    hProjection

/-- Second endpoint cut: accepted original toAddEquiv identity through an abstract adapter. -/
theorem cubicNativeCanonicalTraceEquiv_toAddMonoidHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := hExt
    letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    (cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv K p hp hp0).toLinearMap.toAddMonoidHom =
      (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0).toAddMonoidHom := by
  let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
  let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : HasExt.{u} X.Modules := hExt
  letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
  letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
  letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
  let tau := @cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv K
    (inferInstance : Field K) p hp hp0
    (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
    ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt
  let additiveTau := @cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K
    (inferInstance : Field K) p hp hp0
    (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
    ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt
  have hTau := @cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv_toAddEquiv K
    (inferInstance : Field K) p hp hp0
    (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
    ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› hExt
  exact nativeLinearEquivAdditiveProjection (V := schemeModuleCohomology X W 2)
    tau additiveTau hTau

end PfaffianDescent.Coray
