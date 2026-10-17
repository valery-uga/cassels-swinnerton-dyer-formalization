import PfaffianDescent.ActualPushforwardTensorLeftUnit
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPushforwardTensorNaturality

/-! The ACTUAL canonical tensor-to-intrinsic-fiber morphism. The target
is f_*f^*T, the unit is the actual pullback/pushforward adjunction unit,
and every tensor/pushforward map is the original one. Its unit square
is proved from the existing genuine pushforward tensor left-unit law.
No projection-formula invertibility is assumed. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Canonical projection-formula morphism with the actual intrinsic
fiber target. This definition contains no chart, generator or chosen
comparison. Invertibility is NOT asserted by the definition. -/
def schemeModuleCanonicalFiberProjection
    {X Z : Scheme.{u}} (f : Z ⟶ X) (T : X.Modules) :
    schemeModuleTensor ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit Z.ringCatSheaf)) T ⟶
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj T) :=
  schemeModuleTensorMap
      (𝟙 ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Z.ringCatSheaf)))
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app T) ≫
    cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f
      (SheafOfModules.unit Z.ringCatSheaf) ((Scheme.Modules.pullback f).obj T) ≫
    (Scheme.Modules.pushforward f).map
      (schemeModuleTensorUnitLeftIso ((Scheme.Modules.pullback f).obj T)).hom

/-- The SAME original residue restriction followed by the actual
canonical fiber projection gives precisely the actual adjunction unit,
through the actual unit-left Iso. No fiber-square certificate is input. -/
theorem schemeModuleCanonicalFiberProjection_unit_square
    {X Z : Scheme.{u}} (f : Z ⟶ X) (T : X.Modules) :
    schemeModuleTensorMap (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f)
        (𝟙 T) ≫ schemeModuleCanonicalFiberProjection f T =
      (schemeModuleTensorUnitLeftIso T).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app T := by
  let Q : X.Modules := (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj T)
  let eta : T ⟶ Q := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app T
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f
  have hsplit : schemeModuleTensorMap q (𝟙 T) ≫
      schemeModuleTensorMap (𝟙 ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit Z.ringCatSheaf))) eta =
      schemeModuleTensorMap (𝟙 (SheafOfModules.unit X.ringCatSheaf)) eta ≫
        schemeModuleTensorMap q (𝟙 Q) := by
    rw [schemeModuleTensorMap_comp, schemeModuleTensorMap_comp]
    simp only [Category.comp_id, Category.id_comp] <;>
      exact congrArg (fun b : T ⟶ Q => schemeModuleTensorMap q b)
        (Category.comp_id eta).symm
  change schemeModuleTensorMap q (𝟙 T) ≫
    (schemeModuleTensorMap (𝟙 _) eta ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f
        (SheafOfModules.unit Z.ringCatSheaf) ((Scheme.Modules.pullback f).obj T) ≫
      (Scheme.Modules.pushforward f).map
        (schemeModuleTensorUnitLeftIso ((Scheme.Modules.pullback f).obj T)).hom) = _
  rw [← Category.assoc, hsplit, Category.assoc]
  rw [actualPushforwardTensorMap_unit_left]
  exact schemeModuleTensorUnitLeftIso_naturality eta

/-- Naturality in the SAME original tensor factor/fiber, without any
chart or transported scalar action. -/
theorem schemeModuleCanonicalFiberProjection_naturality
    {X Z : Scheme.{u}} (f : Z ⟶ X) {T T' : X.Modules} (a : T ⟶ T') :
    schemeModuleTensorMap (𝟙 ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit Z.ringCatSheaf))) a ≫
        schemeModuleCanonicalFiberProjection f T' =
      schemeModuleCanonicalFiberProjection f T ≫
        (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map a) := by
  let P : X.Modules ⥤ Z.Modules := Scheme.Modules.pullback f
  let G : Z.Modules ⥤ X.Modules := Scheme.Modules.pushforward f
  let adj : P ⊣ G := Scheme.Modules.pullbackPushforwardAdjunction f
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  have hUnit : a ≫ adj.unit.app T' = adj.unit.app T ≫ G.map (P.map a) := by
    have h := adj.unit.naturality a
    change a ≫ adj.unit.app T' = adj.unit.app T ≫ G.map (P.map a) at h
    exact h
  have hn : schemeModuleTensorMap (𝟙 (G.obj O)) a ≫
      schemeModuleTensorMap (𝟙 (G.obj O)) (adj.unit.app T') =
      schemeModuleTensorMap (𝟙 (G.obj O)) (adj.unit.app T) ≫
        schemeModuleTensorMap (𝟙 (G.obj O)) (G.map (P.map a)) := by
    rw [schemeModuleTensorMap_comp, schemeModuleTensorMap_comp]
    exact congrArg
      (fun b : T ⟶ G.obj (P.obj T') =>
        schemeModuleTensorMap (𝟙 (G.obj O) ≫ 𝟙 (G.obj O)) b) hUnit
  have hp := cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap_naturality
    f (𝟙 O) (P.map a)
  rw [G.map_id] at hp
  have hl := schemeModuleTensorUnitLeftIso_naturality (P.map a)
  have hgl := congrArg G.map hl
  rw [G.map_comp, G.map_comp] at hgl
  unfold schemeModuleCanonicalFiberProjection
  simp only [Category.assoc]
  rw [← Category.assoc (schemeModuleTensorMap (𝟙 (G.obj O)) a), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (schemeModuleTensorMap (𝟙 (G.obj O)) (G.map (P.map a))), hp]
  simp only [Category.assoc]
  rw [hgl]

end PfaffianDescent
