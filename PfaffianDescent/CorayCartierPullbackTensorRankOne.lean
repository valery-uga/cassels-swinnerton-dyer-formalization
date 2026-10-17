import PfaffianDescent.CorayCartierPullbackRankOne
import PfaffianDescent.CubicClosedPointSerreTensorStalkLocalIso
import PfaffianDescent.CubicClosedPointSerreTensorStalkUnitIso
import PfaffianDescent.LocalExtResidueInjective

/-!
Invertibility of the SAME canonical tensor pullback map from actual
rank-one charts. The genuine open-pushforward zigzag replaces unavailable
global generators; no tensor restriction/IsIso certificate is supplied.
SOURCE ONLY / UNVERIFIED. Root owns compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- A genuine unit chart gives an actual GLOBAL map into the pushforward
of that chart's structure sheaf, through the original restriction unit. -/
def schemeModuleRankOneOpenFrameMap
    {X : Scheme.{u}} (U : X.Opens) (N : X.Modules)
    (eN : (Scheme.Modules.restrictFunctor U.ι).obj N ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    N ⟶ (Scheme.Modules.pushforward U.ι).obj
      (SheafOfModules.unit U.toScheme.ringCatSheaf) :=
  (Scheme.Modules.restrictAdjunction U.ι).unit.app N ≫
    (Scheme.Modules.pushforward U.ι).map eN.hom

/-- The same chart map is invertible on its actual chart. Invertibility
of the restriction unit follows from the installed invertible counit and
the original triangle law, not from a desired compatibility input. -/
theorem schemeModuleRankOneOpenFrameMap_restrict_isIso
    {X : Scheme.{u}} (U : X.Opens) (N : X.Modules)
    (eN : (Scheme.Modules.restrictFunctor U.ι).obj N ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (schemeModuleRankOneOpenFrameMap U N eN)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let G := Scheme.Modules.pushforward U.ι
  let A := Scheme.Modules.restrictAdjunction U.ι
  letI : IsIso (A.counit.app (R.obj N)) :=
    NatIso.isIso_app_of_isIso (Scheme.Modules.restrictAdjunction U.ι).counit (R.obj N)
  have ht := A.left_triangle_components N
  change R.map (A.unit.app N) ≫ A.counit.app (R.obj N) = 𝟙 (R.obj N) at ht
  letI : IsIso (R.map (A.unit.app N)) := by
    letI : IsIso (R.map (A.unit.app N) ≫ A.counit.app (R.obj N)) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right (R.map (A.unit.app N)) (A.counit.app (R.obj N))
  letI : IsIso (R.map (G.map eN.hom)) :=
    (R.mapIso (G.mapIso eN)).isIso_hom
  change IsIso (R.map (A.unit.app N ≫ G.map eN.hom))
  rw [R.map_comp]
  infer_instance

/-- Actual tensor-map naturality transfers stalk invertibility across a
GLOBAL map which is invertible on a genuine open. Both directions retain
the same original canonical tensor maps and actual pullback/stalk actions. -/
theorem schemeModulePullbackTensorMap_stalk_isIso_iff_of_restrictIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (y : Y) (hy : f y ∈ U)
    {N N' : X.Modules} (g : N ⟶ N')
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map g)] :
    IsIso ((schemeModuleStalkModuleFunctor Y y).map
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N)) ↔
    IsIso ((schemeModuleStalkModuleFunctor Y y).map
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N')) := by
  let V := f ⁻¹ᵁ U
  let yv : V := ⟨y, hy⟩
  let P := Scheme.Modules.pullback f
  let S := schemeModuleStalkModuleFunctor Y y
  let a := P.map (schemeModuleTensorMap (𝟙 M) g)
  let b := schemeModuleTensorMap (P.map (𝟙 M)) (P.map g)
  let c := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N
  let d := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N'
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
    cubicClosedPointSerreTensorStalk_map_isIso_of_restrict V yv a
  letI : IsIso (S.map b) :=
    cubicClosedPointSerreTensorStalk_map_isIso_of_restrict V yv b
  have h : a ≫ d = c ≫ b :=
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality f (𝟙 M) g
  have hS : S.map a ≫ S.map d = S.map c ≫ S.map b := by
    simpa only [Functor.map_comp] using congrArg S.map h
  change IsIso (S.map c) ↔ IsIso (S.map d)
  constructor
  · intro hc
    letI := hc
    letI : IsIso (S.map a ≫ S.map d) := by
      rw [hS]
      infer_instance
    exact IsIso.of_isIso_comp_left (S.map a) (S.map d)
  · intro hd
    letI := hd
    letI : IsIso (S.map c ≫ S.map b) := by
      rw [← hS]
      infer_instance
    exact IsIso.of_isIso_comp_right (S.map c) (S.map b)

/-- Local rank one suffices for the SAME canonical pullback tensor map.
For each chart, compare N and O_X through their two genuine maps to
U_*O_U. Naturality transfers the proved unit case at every actual stalk. -/
theorem schemeModulePullbackTensorMap_isIso_of_locallyRankOne
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (hN : schemeModuleLocallyRankOne N) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N) := by
  apply schemeModuleMap_isIso_of_stalk
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := hN (f y)
  let O := SheafOfModules.unit X.ringCatSheaf
  let B := (Scheme.Modules.pushforward U.ι).obj (SheafOfModules.unit U.toScheme.ringCatSheaf)
  let eN := schemeModuleRankOneRestrictUnitIso N U e
  let eO := Scheme.Modules.restrictUnitIso U.ι
  let gN : N ⟶ B := schemeModuleRankOneOpenFrameMap U N eN
  let gO : O ⟶ B := schemeModuleRankOneOpenFrameMap U O eO
  letI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map gN) :=
    schemeModuleRankOneOpenFrameMap_restrict_isIso U N eN
  letI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map gO) :=
    schemeModuleRankOneOpenFrameMap_restrict_isIso U O eO
  letI : IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M O) :=
    cubicClosedPointSerreTensorStalk_pullbackTensorMap_unit_isIso f M
  have hB : IsIso ((schemeModuleStalkModuleFunctor Y y).map
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M B)) :=
    (schemeModulePullbackTensorMap_stalk_isIso_iff_of_restrictIso f M U y hy gO).mp
      (inferInstance : IsIso ((schemeModuleStalkModuleFunctor Y y).map
        (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M O)))
  exact (schemeModulePullbackTensorMap_stalk_isIso_iff_of_restrictIso f M U y hy gN).mpr hB

/-- Ordinary Iso on the SAME native map, with no additional frame input. -/
def schemeModulePullbackTensorIsoOfLocallyRankOne
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules)
    (hN : schemeModuleLocallyRankOne N) :
    (Scheme.Modules.pullback f).obj (schemeModuleTensor M N) ≅
      schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) := by
  letI := schemeModulePullbackTensorMap_isIso_of_locallyRankOne f M N hN
  exact asIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N)

end PfaffianDescent
end
