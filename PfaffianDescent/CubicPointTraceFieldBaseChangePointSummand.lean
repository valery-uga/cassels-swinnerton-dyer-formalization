import PfaffianDescent.CubicPointTraceFieldBaseChangeRationalPoint
import PfaffianDescent.CubicPointTraceFieldBaseChangeModule
import PfaffianDescent.ExtMapFixedSource

/-! # The rational diagonal point as a summand of the actual extended support

The two maps below are actual pushforwards of the constructed diagonal
restriction and its separability section. Their composite on the rational
point is the identity; their opposite composite is the diagonal projector.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicPointTraceFieldBaseChange_unitPushforward_congr
    {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) :
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f ≫
      (Scheme.Modules.pushforwardCongr h).hom.app
        (SheafOfModules.unit A.ringCatSheaf) =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit g := by
  cases h
  ext U
  change (((Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app
    (SheafOfModules.unit A.ringCatSheaf)).app U.unop).hom _ = _
  rw [Scheme.Modules.pushforwardCongr_hom_app_app]
  simp
  rfl

/-- Actual unit restriction is compatible with composition of arbitrary
scheme morphisms through the canonical pushforward comparison. -/
theorem cubicPointTraceFieldBaseChange_unitPushforward_comp
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit g ≫
      (Scheme.Modules.pushforward g).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        (SheafOfModules.unit A.ringCatSheaf) =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (f ≫ g) :=
  (BundleSectionZeroLocus.unitToPushforwardObjUnit_comp f g).symm

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The actual tensor-spectrum model of the extended original point in the
extended ambient scheme. -/
def cubicPointTraceFieldBaseChangeTensorPointToAmbient :
    Spec (.of (L ⊗[K] L)) ⟶ schemeBaseChangeToField (L := L) X p :=
  (pullbackSpecIso K L L).inv ≫
    finitePointBaseChangeToAmbient (L := L) p i hi

/-- The tensor diagonal component maps to the canonical residue-field
rational lift, as an equality of actual scheme morphisms. -/
theorem cubicPointTraceFieldBaseChangeTensorDiagonal_comp_ambient :
    cubicPointTraceFieldBaseChangeTensorDiagonal K L ≫
      cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi =
        cubicPointTraceFieldBaseChangeRationalPoint K L p i hi := by
  rw [cubicPointTraceFieldBaseChangeRationalPoint_eq_diagonal,
    cubicPointTraceFieldBaseChangeDiagonalPoint_eq_tensor]
  rfl

instance cubicPointTraceFieldBaseChangeTensorPointToAmbient_isClosedImmersion
    [IsClosedImmersion i] :
    IsClosedImmersion (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi) := by
  unfold cubicPointTraceFieldBaseChangeTensorPointToAmbient
  infer_instance

/-- The structure sheaf of the entire actual extended point support,
pushed into the extended ambient scheme. -/
def cubicPointTraceFieldBaseChangeExtendedPointPushforward :
    (schemeBaseChangeToField (L := L) X p).Modules :=
  (Scheme.Modules.pushforward
    (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).obj
      (SheafOfModules.unit (Spec (.of (L ⊗[K] L))).ringCatSheaf)

/-- The actual direct image of the canonical rational point on the extended
ambient scheme. -/
def cubicPointTraceFieldBaseChangeRationalPointPushforward :
    (schemeBaseChangeToField (L := L) X p).Modules :=
  (Scheme.Modules.pushforward
    (cubicPointTraceFieldBaseChangeRationalPoint K L p i hi)).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)

/-- Composition of actual scheme pushforwards identifies the diagonal
summand with the actual rational point pushforward. -/
def cubicPointTraceFieldBaseChangeDiagonalAmbientPushforwardIso :
    (Scheme.Modules.pushforward
      (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).obj
        (cubicPointTraceFieldBaseChangeDiagonalPushforward K L) ≅
      cubicPointTraceFieldBaseChangeRationalPointPushforward K L p i hi :=
  (Scheme.Modules.pushforwardComp
      (cubicPointTraceFieldBaseChangeTensorDiagonal K L)
      (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).app
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) ≪≫
    (Scheme.Modules.pushforwardCongr
      (cubicPointTraceFieldBaseChangeTensorDiagonal_comp_ambient K L p i hi)).app
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)

/-- The actual restriction from the entire extended point support onto
its diagonal rational component. -/
def cubicPointTraceFieldBaseChangePointSummandRestriction :
    cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi ⟶
      cubicPointTraceFieldBaseChangeRationalPointPushforward K L p i hi :=
  (Scheme.Modules.pushforward
      (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).map
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (cubicPointTraceFieldBaseChangeTensorDiagonal K L)) ≫
    (cubicPointTraceFieldBaseChangeDiagonalAmbientPushforwardIso K L p i hi).hom

/-- The actual restriction from the ambient unit to the entire support,
then to the diagonal summand, is exactly the canonical rational-point
restriction. -/
theorem cubicPointTraceFieldBaseChangePointSummandRestriction_unit :
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi) ≫
      cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi =
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (cubicPointTraceFieldBaseChangeRationalPoint K L p i hi) := by
  let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
  let j := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi
  let h := cubicPointTraceFieldBaseChangeTensorDiagonal_comp_ambient K L p i hi
  have hc : IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j ≫
      (Scheme.Modules.pushforward j).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit d) ≫
      (Scheme.Modules.pushforwardComp d j).hom.app
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (d ≫ j) :=
    (BundleSectionZeroLocus.unitToPushforwardObjUnit_comp d j).symm
  change _ ≫ ((Scheme.Modules.pushforward j).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit d) ≫
      ((Scheme.Modules.pushforwardComp d j).hom.app
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) ≫
        (Scheme.Modules.pushforwardCongr h).hom.app
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))) = _
  exact (congrArg (fun t => t ≫ (Scheme.Modules.pushforwardCongr h).hom.app
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) hc).trans
    (cubicPointTraceFieldBaseChange_unitPushforward_congr h)

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The actual inclusion of the rational point summand selected by the
separability projector. -/
def cubicPointTraceFieldBaseChangePointSummandSection :
    cubicPointTraceFieldBaseChangeRationalPointPushforward K L p i hi ⟶
      cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi :=
  (cubicPointTraceFieldBaseChangeDiagonalAmbientPushforwardIso K L p i hi).inv ≫
    (Scheme.Modules.pushforward
      (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).map
        (cubicPointTraceFieldBaseChangeDiagonalSheafSection K L)

/-- The actual diagonal rational point is a retract of the actual support
obtained by extending the original closed point to its residue field. -/
theorem cubicPointTraceFieldBaseChangePointSummandSection_restriction :
    cubicPointTraceFieldBaseChangePointSummandSection K L p i hi ≫
      cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi = 𝟙 _ := by
  let F := Scheme.Modules.pushforward
    (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)
  let e := cubicPointTraceFieldBaseChangeDiagonalAmbientPushforwardIso K L p i hi
  let s := cubicPointTraceFieldBaseChangeDiagonalSheafSection K L
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (cubicPointTraceFieldBaseChangeTensorDiagonal K L)
  change (e.inv ≫ F.map s) ≫ (F.map q ≫ e.hom) = _
  simp only [Category.assoc]
  rw [← Category.assoc (F.map s), ← F.map_comp,
    cubicPointTraceFieldBaseChangeDiagonalSheafSection_quotient K L, F.map_id]
  simp

/-- The opposite composite is precisely the pushforward of multiplication
by the constructed tensor diagonal projector. -/
theorem cubicPointTraceFieldBaseChangePointSummandRestriction_section :
    cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi ≫
      cubicPointTraceFieldBaseChangePointSummandSection K L p i hi =
    (Scheme.Modules.pushforward
      (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).map
        (cubicPointTraceFieldBaseChangeDiagonalSheafProjector K L) := by
  let F := Scheme.Modules.pushforward
    (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)
  let e := cubicPointTraceFieldBaseChangeDiagonalAmbientPushforwardIso K L p i hi
  let s := cubicPointTraceFieldBaseChangeDiagonalSheafSection K L
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (cubicPointTraceFieldBaseChangeTensorDiagonal K L)
  change (F.map q ≫ e.hom) ≫ (e.inv ≫ F.map s) = F.map (q ≫ s)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (F.map_comp q s).symm

variable [HasExt.{u} (schemeBaseChangeToField (L := L) X p).Modules]
  (Y : (schemeBaseChangeToField (L := L) X p).Modules) (n : ℕ)

/-- Every actual rational-point Ext class survives inclusion into the
entire extended point support, and the constructed section recovers it. -/
theorem cubicPointTraceFieldBaseChangePointSummandExtClass_section
    (z : Ext.{u} (cubicPointTraceFieldBaseChangeRationalPointPushforward K L p i hi) Y n) :
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules) (cubicPointTraceFieldBaseChangePointSummandSection K L p i hi)).comp
      ((Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules) (cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi)).comp
        z (zero_add n)) (zero_add n) = z := by
  rw [Ext.mk₀_comp_mk₀_assoc,
    cubicPointTraceFieldBaseChangePointSummandSection_restriction K L p i hi]
  exact Ext.mk₀_id_comp z

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- Actual source restriction to the ambient unit agrees with restriction
through the diagonal summand, for every Yoneda class and every degree. -/
theorem cubicPointTraceFieldBaseChangePointSummandExtClass_unit
    (z : Ext.{u} (cubicPointTraceFieldBaseChangeRationalPointPushforward K L p i hi) Y n) :
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules) (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi))).comp
      ((Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules) (cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi)).comp
        z (zero_add n)) (zero_add n) =
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules) (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (cubicPointTraceFieldBaseChangeRationalPoint K L p i hi))).comp z (zero_add n) := by
  rw [Ext.mk₀_comp_mk₀_assoc,
    cubicPointTraceFieldBaseChangePointSummandRestriction_unit K L p i hi]

theorem cubicPointTraceFieldBaseChangePointSummandExtClass_injective :
    Function.Injective (fun z : Ext.{u}
        (cubicPointTraceFieldBaseChangeRationalPointPushforward K L p i hi) Y n =>
      (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules) (cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi)).comp
        z (zero_add n)) := by
  intro z w h
  have hs := congrArg
    (fun a => (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules) (cubicPointTraceFieldBaseChangePointSummandSection K L p i hi)).comp
      a (zero_add n)) h
  simpa only [cubicPointTraceFieldBaseChangePointSummandExtClass_section K L p i hi Y n]
    using hs

end
end PfaffianDescent
