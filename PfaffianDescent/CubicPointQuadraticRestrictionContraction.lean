import PfaffianDescent.CubicPointCompatibleQuadraticResidue
import PfaffianDescent.VoisinMixedTwistLocal

/-! # Normalized actual stalk contraction

A perfect tensor pairing and a free coordinate on its right factor induce
a free coordinate on the left factor. The correction below normalizes the
local tensor comparison against the supplied actual right-factor coordinate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

variable {X : Scheme.{u}} (U : X.Opens) (x : U) (Y : X.Modules)
  (eY : (SheafOfModules.overFunctor X.ringCatSheaf U).obj Y ≅
    SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
      (SheafOfModules.commRingSheafOver X.sheaf U)))

local notation "S" => schemeModuleStalkModuleFunctor X (U.ι x)
local notation "R" => X.presheaf.stalk (U.ι x)
local notation "O" => SheafOfModules.unit X.ringCatSheaf

/-- The right-factor coordinate retained by the actual local tensor comparison. -/
def cubicPointQuadraticRestrictionTensorRightCoordinate :
    (S).obj Y ≅ ModuleCat.of R R :=
  (S).mapIso (schemeModuleTensorUnitLeftIso Y).symm ≪≫
    schemeModuleTensorStalkModuleIsoOfLocalTrivialization U x O Y eY ≪≫
    schemeModuleUnitStalkIso X (U.ι x)

/-- A compatible left-factor coordinate induced by an actual perfect pairing.
Every factor is an actual stalk isomorphism. -/
def cubicPointQuadraticRestrictionContractionCoordinate
    (P N : X.Modules) (pair : schemeModuleTensor P Y ≅ N)
    (qY : (S).obj Y ≅ ModuleCat.of R R) (qN : (S).obj N ≅ ModuleCat.of R R) :
    (S).obj P ≅ ModuleCat.of R R :=
  (schemeModuleTensorStalkModuleIsoOfLocalTrivialization U x P Y eY).symm ≪≫
    (S).mapIso pair ≪≫ qN ≪≫ qY.symm ≪≫
    cubicPointQuadraticRestrictionTensorRightCoordinate U x Y eY

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the actual module-valued local tensor stalk comparison. -/
theorem cubicPointQuadraticRestrictionTensorStalk_naturality
    {M N : X.Modules} (f : M ⟶ N) :
    (S).map (schemeModuleTensorMap f (𝟙 Y)) ≫
      (schemeModuleTensorStalkModuleIsoOfLocalTrivialization U x N Y eY).hom =
    (schemeModuleTensorStalkModuleIsoOfLocalTrivialization U x M Y eY).hom ≫
      (S).map f := by
  ext z
  exact ConcreteCategory.congr_hom
    (schemeModuleTensorStalkIsoOfLocalTrivialization_naturality U x eY f) z

set_option backward.isDefEq.respectTransparency false in
/-- The normalized coordinate evaluates a section through the actual tensor
pairing at the generator specified by `qY`. No compatibility premise is needed. -/
theorem cubicPointQuadraticRestrictionContractionCoordinate_section
    (P N : X.Modules) (pair : schemeModuleTensor P Y ≅ N)
    (qY : (S).obj Y ≅ ModuleCat.of R R) (qN : (S).obj N ≅ ModuleCat.of R R)
    (a : O ⟶ P) :
    (cubicPointQuadraticRestrictionContractionCoordinate U x Y eY P N pair qY qN).hom
      ((S).map a ((schemeModuleUnitStalkIso X (U.ι x)).inv 1)) =
    ((S).map ((schemeModuleTensorUnitLeftIso Y).inv ≫
      schemeModuleTensorMap a (𝟙 Y) ≫ pair.hom) ≫ qN.hom) (qY.inv 1) := by
  let t (M : X.Modules) :=
    schemeModuleTensorStalkModuleIsoOfLocalTrivialization U x M Y eY
  let q₀ := cubicPointQuadraticRestrictionTensorRightCoordinate U x Y eY
  let c : ModuleCat.of R R ≅ ModuleCat.of R R := qY.symm ≪≫ q₀
  let b := (schemeModuleTensorUnitLeftIso Y).inv ≫
    schemeModuleTensorMap a (𝟙 Y) ≫ pair.hom
  have hn := cubicPointQuadraticRestrictionTensorStalk_naturality U x Y eY a
  have hn' : (S).map a ≫ (t P).inv = (t O).inv ≫
      (S).map (schemeModuleTensorMap a (𝟙 Y)) := by
    apply (cancel_mono (t P).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp
  have hbase :
      ((t P).inv ≫ (S).map pair.hom ≫ qN.hom)
        ((S).map a ((schemeModuleUnitStalkIso X (U.ι x)).inv 1)) =
      (q₀.inv ≫ (S).map b ≫ qN.hom) 1 := by
    change ((S).map a ≫ (t P).inv ≫ (S).map pair.hom ≫ qN.hom)
      ((schemeModuleUnitStalkIso X (U.ι x)).inv 1) = _
    simp only [← Category.assoc]
    rw [hn']
    simp only [q₀, cubicPointQuadraticRestrictionTensorRightCoordinate, b,
      Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Functor.map_comp,
      Category.assoc]
    have hcancel : (S).map (schemeModuleTensorUnitLeftIso Y).hom ≫
        (S).map (schemeModuleTensorUnitLeftIso Y).inv = 𝟙 _ := by
      rw [← (S).map_comp, Iso.hom_inv_id]
      exact (S).map_id _
    rw [← Category.assoc ((S).map (schemeModuleTensorUnitLeftIso Y).hom)
      ((S).map (schemeModuleTensorUnitLeftIso Y).inv), hcancel, Category.id_comp]
    rfl
  have hgen : qY.inv 1 = c.hom 1 • q₀.inv 1 := by
    apply (ConcreteCategory.bijective_of_isIso q₀.hom).1
    change c.hom 1 = q₀.hom (c.hom 1 • q₀.inv 1)
    rw [q₀.hom.hom.map_smul, Iso.inv_hom_id_apply]
    simp only [smul_eq_mul, mul_one]
  have hc (r : R) : c.hom r = r * c.hom 1 := by
    calc
      c.hom r = c.hom (r • (1 : R)) := by simp
      _ = r • c.hom 1 := c.hom.hom.map_smul r 1
      _ = r * c.hom 1 := rfl
  change c.hom
    (((t P).inv ≫ (S).map pair.hom ≫ qN.hom)
      ((S).map a ((schemeModuleUnitStalkIso X (U.ι x)).inv 1))) =
    ((S).map b ≫ qN.hom) (qY.inv 1)
  rw [hbase, hgen, ((S).map b ≫ qN.hom).hom.map_smul, hc]
  change ((S).map b ≫ qN.hom) (q₀.inv 1) * c.hom 1 =
    c.hom 1 * ((S).map b ≫ qN.hom) (q₀.inv 1)
  exact mul_comm _ _

end PfaffianDescent
