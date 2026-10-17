import PfaffianDescent.CubicIntrinsicCanonicalTraceScalar
import PfaffianDescent.ProjectiveBaseConstantFraction
import PfaffianDescent.SchemeModuleBaseLinearCategory

/-! Original hypersurfaceToBase linearity of the SAME Laurent-normalized trace. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The native base-scalar coefficient map equals the actual homogeneous map. -/
theorem cubicNegativeTwist_scalarEndomorphism_eq_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ) (c : K) :
    Coray.schemeModuleHomBaseSmul
        (X := Proj (grading (equationIdeal p hp))) (hypersurfaceToBase p hp) c
        (𝟙 (show (Proj (grading (equationIdeal p hp))).Modules from
          sheafOfModules (grading (equationIdeal p hp)) m)) =
      (show (sheafOfModules (grading (equationIdeal p hp)) m :
          (Proj (grading (equationIdeal p hp))).Modules) ⟶
        (sheafOfModules (grading (equationIdeal p hp)) m :
          (Proj (grading (equationIdeal p hp))).Modules) from
        mulHomogeneous (grading (equationIdeal p hp))
          (cubicScalarHomogeneous K p hp c) m) := by
  let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
  let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) m
  let pi : X ⟶ Spec (CommRingCat.of K) := hypersurfaceToBase p hp
  let idW : W ⟶ W := 𝟙 W
  refine Coray.schemeModuleHom_ext_sections (X := X) ?_
  intro U s
  have hLeft := Coray.schemeModuleHomBaseSmul_apply pi c idW U s
  have hId : idW.val.app (op U) s = s := rfl
  have hRight := cubicScalarHomogeneous_app_eq_base_constant_smul p hp c m U s
  rw [hId] at hLeft
  exact hLeft.trans hRight.symm

/-- Bounded native Ext scalar bridge; no trace is unfolded here. -/
private theorem cubicNativeH2_smul_eq_homogeneous_postcomp
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hExt : HasExt.{u} (hypersurface p hp).Modules] (c : K) :
    letI : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules := hExt
    letI : Linear K (Proj (grading (equationIdeal p hp))).Modules :=
      Coray.schemeModulesLinearOver (hypersurfaceToBase p hp)
    ∀ z : schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
        (show (Proj (grading (equationIdeal p hp))).Modules from
          sheafOfModules (grading (equationIdeal p hp)) 1) 2,
      c • z = z.comp (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp))
        (cubicScalarHomogeneous K p hp c) 1)) (add_zero 2) := by
  letI : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules := hExt
  letI : Linear K (Proj (grading (equationIdeal p hp))).Modules :=
    Coray.schemeModulesLinearOver (hypersurfaceToBase p hp)
  intro z
  let W : (Proj (grading (equationIdeal p hp))).Modules :=
    sheafOfModules (grading (equationIdeal p hp)) 1
  have hScalar := Coray.schemeModuleExt_smul_eq_actual_postcomp
    (X := Proj (grading (equationIdeal p hp))) (N := W)
    (hypersurfaceToBase p hp) z c
  have hCoefficient : Coray.schemeModuleHomBaseSmul (hypersurfaceToBase p hp) c (𝟙 W) =
      mulHomogeneous (grading (equationIdeal p hp)) (cubicScalarHomogeneous K p hp c) 1 :=
    cubicNegativeTwist_scalarEndomorphism_eq_mulHomogeneous K p hp 1 c
  exact hScalar.trans (congrArg
    (fun f : W ⟶ W => z.comp (Ext.mk₀ f) (add_zero 2)) hCoefficient)

/-- Genuine scalar compatibility for the independently ORIGINAL base action. -/
theorem cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv_smul
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] (c : K) :
    letI : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules := hExt
    letI : Linear K (Proj (grading (equationIdeal p hp))).Modules :=
      Coray.schemeModulesLinearOver (hypersurfaceToBase p hp)
    ∀ z : schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
        (show (Proj (grading (equationIdeal p hp))).Modules from
          sheafOfModules (grading (equationIdeal p hp)) 1) 2,
      cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0 (c • z) =
        c • cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0 z := by
  letI : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules := hExt
  letI : Linear K (Proj (grading (equationIdeal p hp))).Modules :=
    Coray.schemeModulesLinearOver (hypersurfaceToBase p hp)
  intro z
  exact (congrArg (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0)
    (cubicNativeH2_smul_eq_homogeneous_postcomp K p hp c z)).trans
      (cubicIntrinsicCanonicalTrace_scalar_multiplication K p hp hp0 c z)

/-- The literal accepted trace equivalence with its ORIGINAL K-linear action. -/
def cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := hExt
    letI : Linear K X.Modules :=
      Coray.schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    schemeModuleCohomology X W 2 ≃ₗ[K] K := by
  let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
  let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : HasExt.{u} X.Modules := hExt
  letI : Linear K X.Modules :=
    Coray.schemeModulesLinearOver (hypersurfaceToBase p hp)
  letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
  letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
  exact
    { toAddEquiv := (show schemeModuleCohomology X W 2 ≃+ K from
        cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0)
      map_smul' := cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv_smul K p hp hp0 }

/-- No replacement or normalization of the original additive trace occurred. -/
theorem cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv_toAddEquiv
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := hExt
    letI : Linear K X.Modules :=
      Coray.schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    (cubicIntrinsicNegativeOneCohomologyTwoTraceLinearEquiv K p hp hp0).toAddEquiv =
      cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0 := rfl

end PfaffianDescent.ProjectiveNegativeTwist
