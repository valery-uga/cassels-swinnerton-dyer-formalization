import PfaffianDescent.ActualPointChartNativeFiberUnitFactor207
import PfaffianDescent.FieldPointExtCoordinate

/-! SOURCE ONLY207. Canonical actual source-field coordinates of the actual
point-pushforward unit stalk. Actual chart evaluation is derived from the
native factor, and original residue-point normalization is native geometry. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual stalk-pushforward and actual structure-sheaf stalk coordinate,
followed by the already existing canonical field-spectrum stalk equivalence. -/
def actualFieldPointPushforwardUnitStalkCoordinate207
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (y : Spec (.of L)) :
    (((Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk
        (i y)) → L := fun a =>
  specFieldStalkRingEquivAt y
    ((presheafOfModules_unitStalkLinearEquiv (Spec (.of L)).presheaf y).symm
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf y a))

/-- The canonical coordinate sends the literal actual quotient value to the
literal original stalk-ring map. This is the existing native unit calculation. -/
theorem actualFieldPointPushforwardUnitStalkCoordinate_fromRing207
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (y : Spec (.of L)) (r : X.presheaf.stalk (i y)) :
    actualFieldPointPushforwardUnitStalkCoordinate207 i y
      (closedImmersionPushforwardStalkFromRingLinearMap i (i y) r) =
      specFieldStalkRingEquivAt y (i.stalkMap y r) :=
  congrArg (specFieldStalkRingEquivAt y)
    (closedImmersionPushforwardStalkFromRingLinearMap_comp_stalkPushforward i y r)

/-- Exact native chart fiber-unit evaluation in the actual canonical point
residue coordinate. No residue/fiber comparison or scalar normalization input. -/
theorem actualDualChartFiberUnitMap_stalkCoordinate207
    {L : Type u} [Field L] {X : Scheme.{u}}
    (U : X.Opens) (j : Spec (.of L) ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)] (y : Spec (.of L)) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (a : (schemeModuleStalkModuleFunctor X (U.ι (j y))).obj (dual M)) :
    actualFieldPointPushforwardUnitStalkCoordinate207 (j ≫ U.ι) y
        (((schemeModuleStalkModuleFunctor X (U.ι (j y))).map
          (actualPointChartFiberUnitMap207 U j (dual M) (dualRestrictUnitIso U e))) a) =
      closedFieldPointResidueRingEquivAt (j ≫ U.ι) y
        (X.residue (U.ι (j y))
          ((actualDualFrameNativeStalkIso191 U (j y) M e).hom a)) := by
  have h := ConcreteCategory.congr_hom
    (actualDualChartFiberUnitMap_native_factor207 U j y M e) a
  change (((schemeModuleStalkModuleFunctor X (U.ι (j y))).map
      (actualPointChartFiberUnitMap207 U j (dual M) (dualRestrictUnitIso U e))) a) =
    closedImmersionPushforwardStalkFromRingLinearMap (j ≫ U.ι) (U.ι (j y))
      ((actualDualFrameNativeStalkIso191 U (j y) M e).hom a) at h
  have hCoordinate := congrArg
    (actualFieldPointPushforwardUnitStalkCoordinate207 (j ≫ U.ι) y) h
  have hRing := actualFieldPointPushforwardUnitStalkCoordinate_fromRing207 (j ≫ U.ι) y
    ((actualDualFrameNativeStalkIso191 U (j y) M e).hom a)
  exact hCoordinate.trans (hRing.trans
    (closedFieldPointResidueRingEquivAt_residue_eq_stalkMap (j ≫ U.ι) y _).symm)

/-- Pin the native local hom for the bundled ORIGINAL residue field. -/
private theorem originalResiduePoint_isLocalHom207 (X : Scheme.{u}) (x : X) :
    IsLocalHom (Scheme.stalkClosedPointTo (X.fromSpecResidueField x)).hom :=
  Scheme.isLocalHom_stalkClosedPointTo (R := X.residueField x) (X.fromSpecResidueField x)

attribute [local instance] originalResiduePoint_isLocalHom207

/-- Native Spec/field equivalence identifies the ORIGINAL residue-point map
with its identity residue embedding, including its literal image-point cast. -/
theorem originalResiduePoint_descStalk_eq207
    (X : Scheme.{u}) (x : X) :
    (@Scheme.descResidueField (X.residueField x) inferInstance X
      (X.fromSpecResidueField x (closedPoint (CommRingCat.of (X.residueField x))))
      (Scheme.stalkClosedPointTo (X.fromSpecResidueField x))
      (originalResiduePoint_isLocalHom207 X x)) =
      (X.residueFieldCongr (Scheme.fromSpecResidueField_apply x
        (closedPoint (CommRingCat.of (X.residueField x))))).hom := by
  have h := (Scheme.SpecToEquivOfField (X.residueField x) X).apply_symm_apply
    ⟨x, 𝟙 (X.residueField x)⟩
  change (Scheme.SpecToEquivOfField (X.residueField x) X)
      (Spec.map (𝟙 (X.residueField x)) ≫ X.fromSpecResidueField x) =
    ⟨x, 𝟙 (X.residueField x)⟩ at h
  rw [Spec.map_id] at h
  have hid : (𝟙 (Spec (X.residueField x))) ≫ X.fromSpecResidueField x =
      X.fromSpecResidueField x := Category.id_comp (X.fromSpecResidueField x)
  have hPoint := (congrArg (Scheme.SpecToEquivOfField (X.residueField x) X) hid).symm.trans h
  have h' : (⟨X.fromSpecResidueField x (closedPoint (CommRingCat.of (X.residueField x))),
        (@Scheme.descResidueField (X.residueField x) inferInstance X
      (X.fromSpecResidueField x (closedPoint (CommRingCat.of (X.residueField x))))
      (Scheme.stalkClosedPointTo (X.fromSpecResidueField x))
      (originalResiduePoint_isLocalHom207 X x))⟩ :
      Σ z : X, X.residueField z ⟶ CommRingCat.of (X.residueField x)) =
        ⟨x, 𝟙 (X.residueField x)⟩ := by
    change (Scheme.SpecToEquivOfField (X.residueField x) X)
      (X.fromSpecResidueField x) = ⟨x, 𝟙 (X.residueField x)⟩
    exact hPoint
  obtain ⟨hx, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp h'
  simpa only [Category.comp_id] using he

/-- A literal factorization of the ORIGINAL residue-point map forces its
field coordinate to be the original residue-field identification. The premise
is only equality of the actual geometric point map, supplied by native lift_fac. -/
theorem actualOriginalResiduePointCoordinate_eq207
    {X : Scheme.{u}} (x : X)
    (i : Spec (X.residueField x) ⟶ X) [IsClosedImmersion i]
    (hi : i = X.fromSpecResidueField x) (y : Spec (X.residueField x)) :
    closedFieldPointResidueRingEquivAt i y =
      (X.residueFieldCongr ((congrArg (fun f => f y) hi).trans
        (Scheme.fromSpecResidueField_apply x y))).commRingCatIsoToRingEquiv := by
  subst i
  have hy : y = closedPoint (CommRingCat.of (X.residueField x)) := Subsingleton.elim _ _
  subst y
  apply RingEquiv.ext
  intro a
  change (@Scheme.descResidueField (X.residueField x) inferInstance X
      (X.fromSpecResidueField x (closedPoint (CommRingCat.of (X.residueField x))))
      (Scheme.stalkClosedPointTo (X.fromSpecResidueField x))
      (originalResiduePoint_isLocalHom207 X x)) a =
    (X.residueFieldCongr (Scheme.fromSpecResidueField_apply x
      (closedPoint (CommRingCat.of (X.residueField x))))).hom a
  rw [originalResiduePoint_descStalk_eq207]

/-- Canonical ORIGINAL residue coordinate of the actual chart fiber map.
The literal geometric factorization is the one constructed by lifting through
U. No fiber comparison, trace comparison or desired nonzero input occurs. -/
theorem actualOriginalPointDualChartFiberUnitMap_residue207
    {X : Scheme.{u}} (x : X) (U : X.Opens)
    (j : Spec (X.residueField x) ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (hji : j ≫ U.ι = X.fromSpecResidueField x)
    (y : Spec (X.residueField x)) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (a : (schemeModuleStalkModuleFunctor X (U.ι (j y))).obj (dual M)) :
    actualFieldPointPushforwardUnitStalkCoordinate207 (j ≫ U.ι) y
        (((schemeModuleStalkModuleFunctor X (U.ι (j y))).map
          (actualPointChartFiberUnitMap207 U j (dual M) (dualRestrictUnitIso U e))) a) =
      (X.residueFieldCongr ((congrArg (fun f => f y) hji).trans
        (Scheme.fromSpecResidueField_apply x y))).hom
          (X.residue (U.ι (j y))
            ((actualDualFrameNativeStalkIso191 U (j y) M e).hom a)) := by
  have hChart := @actualDualChartFiberUnitMap_stalkCoordinate207
    (X.residueField x) inferInstance X U j inferInstance y M e a
  have hPoint := actualOriginalResiduePointCoordinate_eq207 x (j ≫ U.ι) hji y
  have hPointValue := congrArg (fun v => v
    (X.residue (U.ι (j y)) ((actualDualFrameNativeStalkIso191 U (j y) M e).hom a))) hPoint
  change closedFieldPointResidueRingEquivAt (j ≫ U.ι) y
      (X.residue (U.ι (j y)) ((actualDualFrameNativeStalkIso191 U (j y) M e).hom a)) =
    (X.residueFieldCongr ((congrArg (fun f => f y) hji).trans
      (Scheme.fromSpecResidueField_apply x y))).hom
        (X.residue (U.ι (j y)) ((actualDualFrameNativeStalkIso191 U (j y) M e).hom a)) at hPointValue
  exact hChart.trans hPointValue

end PfaffianDescent
