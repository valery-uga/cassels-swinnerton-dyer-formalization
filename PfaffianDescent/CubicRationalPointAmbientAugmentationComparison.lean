import PfaffianDescent.SchemePushforwardUnitSections
import PfaffianDescent.BundleSectionZeroLocus
import PfaffianDescent.ExtMapFixedSource

/-! # Actual unit restriction through a closed point and an ambient immersion

The target comparison is assembled from the original point-unit target
isomorphism and the actual composition isomorphism of scheme pushforwards.
Under that comparison, the original iterated unit restriction is literally
the unit restriction of the composite scheme morphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent
universe u v w

/-- The original ambient unit restriction used by the Cartier criterion. -/
def cubicRationalPointAmbientAugmentation_map
    {Z X A : Scheme.{u}} (i : Z ⟶ X) (j : X ⟶ A) [IsClosedImmersion i] :
    SheafOfModules.unit A.ringCatSheaf ⟶
      (Scheme.Modules.pushforward j).obj
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ :=
  IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j ≫
    (Scheme.Modules.pushforward j).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
        (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)

/-- The actual Cartier point target is canonically the literal pushforward
of the original point along the composite ambient morphism. -/
def cubicRationalPointAmbientAugmentation_targetIso
    {Z X A : Scheme.{u}} (i : Z ⟶ X) (j : X ⟶ A) [IsClosedImmersion i] :
    (Scheme.Modules.pushforward j).obj
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ ≅
      (Scheme.Modules.pushforward (i ≫ j)).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  (Scheme.Modules.pushforward j).mapIso (closedImmersionIdealTwistSequenceUnitTargetIso i) ≪≫
    (Scheme.Modules.pushforwardComp i j).app (SheafOfModules.unit Z.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison square follows from actual unit restriction coherence;
it is not supplied as a premise. -/
theorem cubicRationalPointAmbientAugmentation_map_comp_targetIso
    {Z X A : Scheme.{u}} (i : Z ⟶ X) (j : X ⟶ A) [IsClosedImmersion i] :
    cubicRationalPointAmbientAugmentation_map i j ≫
      (cubicRationalPointAmbientAugmentation_targetIso i j).hom =
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ≫ j) := by
  let F := Scheme.Modules.pushforward j
  let e := closedImmersionIdealTwistSequenceUnitTargetIso i
  let a := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j
  let b := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let c := (Scheme.Modules.pushforwardComp i j).hom.app (SheafOfModules.unit Z.ringCatSheaf)
  have hb : (b ≫ e.inv) ≫ e.hom = b := by
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  have hmap : F.map (b ≫ e.inv) ≫ F.map e.hom = F.map b :=
    (F.map_comp (b ≫ e.inv) e.hom).symm.trans (congrArg F.map hb)
  change (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j ≫
      F.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫ e.inv)) ≫
        (F.map e.hom ≫ (Scheme.Modules.pushforwardComp i j).hom.app
          (SheafOfModules.unit Z.ringCatSheaf)) = _
  calc
    (a ≫ F.map (b ≫ e.inv)) ≫ (F.map e.hom ≫ c) =
        a ≫ (F.map (b ≫ e.inv) ≫ F.map e.hom) ≫ c := by simp only [Category.assoc]
    _ = a ≫ F.map b ≫ c := congrArg (fun t => a ≫ t ≫ c) hmap
    _ = _ := (BundleSectionZeroLocus.unitToPushforwardObjUnit_comp i j).symm

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of Ext pullback is invariant under an actual isomorphism
of augmentation targets. This is a purely categorical transport lemma. -/
theorem cubicRationalPointAmbientAugmentation_precomp_injective_of_targetIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {U Q P Y : C} (a : U ⟶ Q) (b : U ⟶ P) (e : Q ≅ P)
    (h : a ≫ e.hom = b) (n : ℕ)
    (hinj : Function.Injective ((Ext.mk₀.{w} b).precomp Y (zero_add n))) :
    Function.Injective ((Ext.mk₀.{w} a).precomp Y (zero_add n)) := by
  have hb : b ≫ e.inv = a := by
    rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  intro z z' hz
  apply (extPrecompIsoOfIso e).injective
  apply hinj
  change (Ext.mk₀.{w} b).comp ((Ext.mk₀.{w} e.inv).comp z (zero_add n)) (zero_add n) =
    (Ext.mk₀.{w} b).comp ((Ext.mk₀.{w} e.inv).comp z' (zero_add n)) (zero_add n)
  rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, hb]
  exact hz

end PfaffianDescent
