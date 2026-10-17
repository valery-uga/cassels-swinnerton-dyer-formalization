import PfaffianDescent.CubicPointTraceFieldBaseChangeIsomorphicSupport
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationSchemeIso

/-! Native support and unit comparison through a genuine Scheme Iso.
All objects are actual pullbacks/pushforwards; no comparison is supplied. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual point fibre of a scheme isomorphism is its original point. -/
def schemeIsoPointPullbackIso223
    {Y Z T : Scheme.{u}} (e : Z ≅ Y) (i : T ⟶ Y) : T ≅ pullback e.hom i :=
  (asIso (pullback.snd e.hom i)).symm

/-- The support Iso preserves the actual embedding, including its endpoint. -/
theorem schemeIsoPointPullbackIso_hom_fst223
    {Y Z T : Scheme.{u}} (e : Z ≅ Y) (i : T ⟶ Y) :
    (schemeIsoPointPullbackIso223 e i).hom ≫ pullback.fst e.hom i = i ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  calc
    ((schemeIsoPointPullbackIso223 e i).hom ≫ pullback.fst e.hom i) ≫ e.hom =
        (schemeIsoPointPullbackIso223 e i).hom ≫ (pullback.snd e.hom i ≫ i) := by
          rw [Category.assoc, pullback.condition]
    _ = i := by
      change inv (pullback.snd e.hom i) ≫ (pullback.snd e.hom i ≫ i) = i
      exact IsIso.inv_hom_id_assoc _ _
    _ = (i ≫ e.inv) ≫ e.hom := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Literal geometric pullback of a point support agrees with the original
point embedded through the inverse scheme isomorphism. -/
def schemeIsoClosedPointPullbackSupportIso223
    {Y Z T : Scheme.{u}} (e : Z ≅ Y) (i : T ⟶ Y) [IsClosedImmersion i] :
    (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit T.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (i ≫ e.inv)).obj (SheafOfModules.unit T.ringCatSheaf) :=
  cubicPointTraceFieldBaseChangeClosedSupportIso e.hom i ≪≫
    cubicPointTraceFieldBaseChangeIsomorphicSupportIso
      (schemeIsoPointPullbackIso223 e i) (pullback.fst e.hom i) ≪≫
    (Scheme.Modules.pushforwardCongr (schemeIsoPointPullbackIso_hom_fst223 e i)).app
      (SheafOfModules.unit T.ringCatSheaf)

/-- The support transport preserves the actual canonical unit quotient. -/
theorem schemeIsoClosedPointPullbackSupportIso_unit223
    {Y Z T : Scheme.{u}} (e : Z ≅ Y) (i : T ⟶ Y) [IsClosedImmersion i] :
    (Scheme.Modules.pullback e.hom).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
      (schemeIsoClosedPointPullbackSupportIso223 e i).hom =
    (cubicPointTraceFieldBaseChangePullbackUnitIso e.hom).hom ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ≫ e.inv) := by
  let C := cubicPointTraceFieldBaseChangeClosedSupportIso e.hom i
  let A := cubicPointTraceFieldBaseChangeIsomorphicSupportIso
    (schemeIsoPointPullbackIso223 e i) (pullback.fst e.hom i)
  let V := (Scheme.Modules.pushforwardCongr (schemeIsoPointPullbackIso_hom_fst223 e i)).app
    (SheafOfModules.unit T.ringCatSheaf)
  have hC : (Scheme.Modules.pullback e.hom).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ C.hom =
      (cubicPointTraceFieldBaseChangePullbackUnitIso e.hom).hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (pullback.fst e.hom i) := by
    exact closedImmersionPushforwardBaseChangeHom_quotient e.hom i
  change _ ≫ (C.hom ≫ (A.hom ≫ V.hom)) = _
  calc
    _ = (((Scheme.Modules.pullback e.hom).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ C.hom) ≫ A.hom) ≫ V.hom := by
          simp only [Category.assoc]
    _ = (((cubicPointTraceFieldBaseChangePullbackUnitIso e.hom).hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (pullback.fst e.hom i)) ≫ A.hom) ≫ V.hom :=
          congrArg (fun a => (a ≫ A.hom) ≫ V.hom) hC
    _ = (cubicPointTraceFieldBaseChangePullbackUnitIso e.hom).hom ≫
        ((IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (pullback.fst e.hom i) ≫ A.hom) ≫ V.hom) := by
          simp only [Category.assoc]
    _ = (cubicPointTraceFieldBaseChangePullbackUnitIso e.hom).hom ≫
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          ((schemeIsoPointPullbackIso223 e i).hom ≫ pullback.fst e.hom i) ≫ V.hom) := by
          rw [cubicPointTraceFieldBaseChangeIsomorphicSupportIso_unit]
    _ = _ := by
      exact congrArg (fun a => (cubicPointTraceFieldBaseChangePullbackUnitIso e.hom).hom ≫ a)
        (cubicPointTraceFieldBaseChange_unitPushforward_congr
          (schemeIsoPointPullbackIso_hom_fst223 e i))

/-- The inverse support square is the precise direction for Ext source
transport. Its maps are all the canonical geometric ones above. -/
theorem schemeIsoClosedPointPullbackSupportIso_unit_inv223
    {Y Z T : Scheme.{u}} (e : Z ≅ Y) (i : T ⟶ Y) [IsClosedImmersion i] :
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ≫ e.inv) ≫
      (schemeIsoClosedPointPullbackSupportIso223 e i).inv =
    (cubicPointTraceFieldBaseChangePullbackUnitIso e.hom).inv ≫
      (Scheme.Modules.pullback e.hom).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) := by
  apply (cancel_mono (schemeIsoClosedPointPullbackSupportIso223 e i).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [schemeIsoClosedPointPullbackSupportIso_unit223, Iso.inv_hom_id_assoc]

end PfaffianDescent
