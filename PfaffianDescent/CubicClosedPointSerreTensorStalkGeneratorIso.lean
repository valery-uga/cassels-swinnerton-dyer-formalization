import PfaffianDescent.CubicClosedPointSerreTensorStalkLocalIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorNaturality
import PfaffianDescent.LocalExtResidueInjective

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Local generators which are actual global unit maps reduce the literal
pullback tensor comparison to its actual unit case. -/
theorem cubicClosedPointSerreTensorStalk_pullbackTensorMap_isIso_of_generators
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    [IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (SheafOfModules.unit Y.ringCatSheaf))]
    (hgen : ∀ x : X, ∃ (U : Y.Opens) (g : SheafOfModules.unit Y.ringCatSheaf ⟶ N),
      f x ∈ U ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map g)) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N) := by
  apply schemeModuleMap_isIso_of_stalk
  intro x
  obtain ⟨U, g, hxU, hg⟩ := hgen x
  letI := hg
  let V := f ⁻¹ᵁ U
  let xv : V := ⟨x, hxU⟩
  let P := Scheme.Modules.pullback f
  let S := schemeModuleStalkModuleFunctor X x
  let a := P.map (schemeModuleTensorMap (𝟙 M) g)
  let b := schemeModuleTensorMap (P.map (𝟙 M)) (P.map g)
  let c := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
    (SheafOfModules.unit Y.ringCatSheaf)
  let d := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N
  letI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (schemeModuleTensorMap (𝟙 M) g)) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U (𝟙 M) g
  letI : IsIso ((Scheme.Modules.restrictFunctor V.ι).map a) :=
    cubicClosedPointSerreTensorStalk_restrict_pullbackMap_isIso f U V le_rfl
      (schemeModuleTensorMap (𝟙 M) g)
  letI : IsIso ((Scheme.Modules.restrictFunctor V.ι).map (P.map g)) :=
    cubicClosedPointSerreTensorStalk_restrict_pullbackMap_isIso f U V le_rfl g
  letI : IsIso ((Scheme.Modules.restrictFunctor V.ι).map b) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso V (P.map (𝟙 M)) (P.map g)
  letI : IsIso (S.map a) :=
    cubicClosedPointSerreTensorStalk_map_isIso_of_restrict V xv a
  letI : IsIso (S.map b) :=
    cubicClosedPointSerreTensorStalk_map_isIso_of_restrict V xv b
  have h : a ≫ d = c ≫ b :=
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality f (𝟙 M) g
  have hS : S.map a ≫ S.map d = S.map c ≫ S.map b := by
    simpa only [Functor.map_comp] using congrArg S.map h
  letI : IsIso (S.map a ≫ S.map d) := by
    rw [hS]
    infer_instance
  exact IsIso.of_isIso_comp_left (S.map a) (S.map d)

end PfaffianDescent
