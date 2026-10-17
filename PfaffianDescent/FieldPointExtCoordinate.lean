import PfaffianDescent.SchemeModuleRestrictStalkLinear
import PfaffianDescent.ClosedFieldPointResidue
import PfaffianDescent.LocalExtResidueInjective
import PfaffianDescent.SchemeModuleGlobalSections
import PfaffianDescent.StalkPushforwardNaturality
import PfaffianDescent.VoisinHypersurfaceCokernel

/-!
# Degree-two Ext coordinates at a closed field point

This file composes the global-to-local complete-intersection calculation with
the canonical identification of the residue field at a closed `L`-point with
`L`.  The only remaining geometric input is the bijectivity of the global
Ext-to-stalk comparison.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u v w

/-- Precomposing a fixed Ext class by an additive family of source
endomorphisms produces an additive family of Ext classes.  This is the
categorical operation used to scale one normalized point-supported Yoneda
class through all residue-field coordinates. -/
noncomputable def extPrecompFixedClassAddHom
    {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
    (M N : C) (n : ℕ) (z : Ext.{u} M N n) :
    (M ⟶ M) →+ Ext.{u} M N n :=
  (Ext.postcomp z M (zero_add n)).comp
    Ext.addEquiv₀.symm.toAddMonoidHom

@[simp]
theorem extPrecompFixedClassAddHom_apply
    {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
    (M N : C) (n : ℕ) (z : Ext.{u} M N n) (a : M ⟶ M) :
    extPrecompFixedClassAddHom M N n z a =
      (Ext.mk₀ a).comp z (zero_add n) := rfl

/-- Multiplication by elements of the residue field, pushed from a closed
field point into the ambient scheme.  This supplies the scalar endomorphisms
used to scale a normalized point-supported Ext class. -/
noncomputable def fieldPointPushforwardScalarEndomorphismAddHom
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) :
    L →+ ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) ⟶
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) where
  toFun a := (Scheme.Modules.pushforward i).map
    (schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) a)
  map_zero' := by
    let F := Scheme.Modules.pushforward i
    let c := schemeModuleConstantEndomorphismAddHom
      (𝟙 (Spec (.of L)))
    calc
      F.map (c 0) = F.map 0 := congrArg F.map c.map_zero
      _ = 0 := F.map_zero _ _
  map_add' a b := by
    let F := Scheme.Modules.pushforward i
    let c := schemeModuleConstantEndomorphismAddHom
      (𝟙 (Spec (.of L)))
    calc
      F.map (c (a + b)) = F.map (c a + c b) := congrArg F.map (c.map_add a b)
      _ = F.map (c a) + F.map (c b) := Functor.map_add _

/-- The same residue-field scalar action after tensoring the point sheaf by
an ambient module.  For the line-bundle twist in Voisin's construction this
is literally the source object of the relevant degree-two Ext group. -/
noncomputable def fieldPointPushforwardTwistScalarEndomorphismAddHom
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (T : X.Modules) :
    L →+ (schemeModuleTensor
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T ⟶
      schemeModuleTensor
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) where
  toFun a := (schemeModuleTensorRight T).map
    (fieldPointPushforwardScalarEndomorphismAddHom i a)
  map_zero' := by
    let F := schemeModuleTensorRight T
    let c := fieldPointPushforwardScalarEndomorphismAddHom i
    calc
      F.map (c 0) = F.map 0 := congrArg F.map c.map_zero
      _ = 0 := F.map_zero _ _
  map_add' a b := by
    let F := schemeModuleTensorRight T
    let c := fieldPointPushforwardScalarEndomorphismAddHom i
    calc
      F.map (c (a + b)) = F.map (c a + c b) := congrArg F.map (c.map_add a b)
      _ = F.map (c a) + F.map (c b) := Functor.map_add _

/-- The germ of the constant function `a` on the spectrum of a field is `a`
under the canonical closed-point stalk isomorphism. -/
theorem specField_stalkClosedPointIso_hom_germ_affineFunctionHom_id
    {L : Type u} [Field L] (a : L) :
    (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of L)).hom
        ((Spec (.of L)).presheaf.germ ⊤
          (IsLocalRing.closedPoint (CommRingCat.of L)) trivial
          (affineFunctionHom (𝟙 (Spec (.of L))) a)) = a := by
  have h := AlgebraicGeometry.germ_stalkClosedPointIso_hom
    (R := CommRingCat.of L)
  have ha := DFunLike.congr_fun (congr_arg ConcreteCategory.hom h)
    (affineFunctionHom (𝟙 (Spec (.of L))) a)
  rw [ConcreteCategory.comp_apply] at ha
  rw [ha]
  dsimp [affineFunctionHom]
  have hi := congr_arg ConcreteCategory.hom
    (Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of L)))
  exact DFunLike.congr_fun hi a

/-- The local ring at any point of `Spec L` is canonically `L`; the point
argument is harmless because the spectrum of a field is a singleton. -/
noncomputable def specFieldStalkRingEquivAt
    {L : Type u} [Field L] (x : Spec (.of L)) :
    (Spec (.of L)).presheaf.stalk x ≃+* L := by
  let h : x = IsLocalRing.closedPoint (CommRingCat.of L) := Subsingleton.elim _ _
  subst x
  exact (AlgebraicGeometry.stalkClosedPointIso
    (CommRingCat.of L)).commRingCatIsoToRingEquiv

/-- The preceding point-independent stalk equivalence sends the germ of the
constant function `a` to `a`. -/
theorem specFieldStalkRingEquivAt_germ_affineFunctionHom_id
    {L : Type u} [Field L] (x : Spec (.of L)) (a : L) :
    specFieldStalkRingEquivAt x
        ((Spec (.of L)).presheaf.germ ⊤ x (Set.mem_univ x)
          (affineFunctionHom (𝟙 (Spec (.of L))) a)) = a := by
  let h : x = IsLocalRing.closedPoint (CommRingCat.of L) := Subsingleton.elim _ _
  subst x
  exact specField_stalkClosedPointIso_hom_germ_affineFunctionHom_id a

/-- The ambient residue-field coordinate of a closed field point agrees with
evaluation in the source local ring followed by its canonical identification
with the field. -/
theorem closedFieldPointResidueRingEquivAt_residue_eq_stalkMap
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L)) (r : X.presheaf.stalk (i x)) :
    closedFieldPointResidueRingEquivAt i x (X.residue (i x) r) =
      specFieldStalkRingEquivAt x (i.stalkMap x r) := by
  let h : x = IsLocalRing.closedPoint (CommRingCat.of L) := Subsingleton.elim _ _
  subst x
  change Scheme.descResidueField (Scheme.stalkClosedPointTo i)
      (X.residue (i (IsLocalRing.closedPoint (CommRingCat.of L))) r) =
    (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of L)).hom
      (i.stalkMap (IsLocalRing.closedPoint (CommRingCat.of L)) r)
  rw [← ConcreteCategory.comp_apply, Scheme.residue_descResidueField]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L)) :
    letI : Module (X.presheaf.stalk (i x))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i (i x)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) := by
  dsimp
  letI : Module (X.presheaf.stalk (i x))
      (((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  let phi : X.presheaf.stalk (i x) →+* L :=
    (specFieldStalkRingEquivAt x).toRingHom.comp (i.stalkMap x).hom
  have hphi : Function.Surjective phi :=
    (specFieldStalkRingEquivAt x).surjective.comp (i.stalkMap_surjective x)
  have hker : RingHom.ker phi =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) :=
    IsLocalRing.ker_eq_maximalIdeal phi hphi
  apply SetLike.ext
  intro r
  rw [LinearMap.mem_ker,
    closedImmersionPushforwardStalkFromRingLinearMap_eq_zero_iff
      i i.isClosedEmbedding.isInducing x r]
  change i.stalkMap x r = 0 ↔ r ∈ IsLocalRing.maximalIdeal _
  rw [← hker]
  change i.stalkMap x r = 0 ↔ phi r = 0
  exact (map_eq_zero_iff (specFieldStalkRingEquivAt x)
    (specFieldStalkRingEquivAt x).injective).symm


/-- A chosen ambient local-ring lift of a scalar in the residue field of a
closed `L`-point. -/
noncomputable def fieldPointScalarLift
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L)) (a : L) : X.presheaf.stalk (i x) :=
  (X.residue_surjective (i x)
    ((closedFieldPointResidueRingEquivAt i x).symm a)).choose

/-- The chosen ambient lift has the prescribed `L`-valued residue. -/
theorem fieldPointScalarLift_residue
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L)) (a : L) :
    closedFieldPointResidueRingEquivAt i x
        (X.residue (i x) (fieldPointScalarLift i x a)) = a := by
  unfold fieldPointScalarLift
  rw [(X.residue_surjective (i x)
    ((closedFieldPointResidueRingEquivAt i x).symm a)).choose_spec]
  exact (closedFieldPointResidueRingEquivAt i x).apply_symm_apply a

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The pushforward-stalk comparison intertwines a scalar endomorphism of a
field point with its pushed-forward endomorphism. -/
theorem fieldPointPushforwardScalarEndomorphism_stalkPushforward
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (x : Spec (.of L)) (a : L)
    (y : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :
    letI : Module (X.presheaf.stalk (i x))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module ((Spec (.of L)).presheaf.stalk x)
        ((show (Spec (.of L)).Modules from
          SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
        (schemeModuleStalkLinearMap
          (fieldPointPushforwardScalarEndomorphismAddHom i a) (i x) y) =
      schemeModuleStalkLinearMap
        (schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) a) x
        (TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x y) := by
  dsimp
  letI : Module (X.presheaf.stalk (i x))
      (((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  letI : Module ((Spec (.of L)).presheaf.stalk x)
      ((show (Spec (.of L)).Modules from
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  let f := schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) a
  have hnat := (presheafStalkPushforwardNatTrans
    (C := AddCommGrpCat) i.base x).naturality
      ((Scheme.Modules.toPresheaf (Spec (.of L))).map f)
  exact DFunLike.congr_fun (congr_arg ConcreteCategory.hom hnat) y

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- After the pushforward-stalk and unit-stalk identifications, the pushed
field scalar acts by multiplication by the germ of that scalar on `Spec L`. -/
theorem fieldPointPushforwardScalarEndomorphism_stalk_multiplication
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (x : Spec (.of L)) (a : L)
    (y : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :
    letI : Module (X.presheaf.stalk (i x))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module ((Spec (.of L)).presheaf.stalk x)
        ((show (Spec (.of L)).Modules from
          SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    let p := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
    let uL := presheafOfModules_unitStalkLinearEquiv (Spec (.of L)).presheaf x
    uL.symm (p (schemeModuleStalkLinearMap
        (fieldPointPushforwardScalarEndomorphismAddHom i a) (i x) y)) =
      (Spec (.of L)).presheaf.germ ⊤ x (Set.mem_univ x)
          (affineFunctionHom (𝟙 (Spec (.of L))) a) *
        uL.symm (p y) := by
  dsimp
  letI : Module (X.presheaf.stalk (i x))
      (((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  letI : Module ((Spec (.of L)).presheaf.stalk x)
      ((show (Spec (.of L)).Modules from
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  let p := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
  let uL := presheafOfModules_unitStalkLinearEquiv (Spec (.of L)).presheaf x
  let b := uL.symm (p y)
  have hpy : p y = uL b := by simp [b]
  rw [fieldPointPushforwardScalarEndomorphism_stalkPushforward]
  rw [hpy]
  rw [uL.symm_apply_apply]
  have hmul := schemeModuleStalkToRingLinearMap_unitEndomorphismOfRegularFunction
    (affineFunctionHom (𝟙 (Spec (.of L))) a) x b
  change uL.symm
      (schemeModuleStalkLinearMap
        (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (affineFunctionHom (𝟙 (Spec (.of L))) a)) x (uL b)) =
    (Spec (.of L)).presheaf.germ ⊤ x (Set.mem_univ x)
      (affineFunctionHom (𝟙 (Spec (.of L))) a) * b at hmul
  exact hmul

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- In the canonical `L`-coordinate on the stalk of the pushed point sheaf,
the pushed scalar endomorphism is ordinary multiplication by `a`. -/
theorem fieldPointPushforwardScalarEndomorphism_stalk_coordinate
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (x : Spec (.of L)) (a : L)
    (y : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :
    letI : Module (X.presheaf.stalk (i x))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module ((Spec (.of L)).presheaf.stalk x)
        ((show (Spec (.of L)).Modules from
          SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    let p := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
    let uL := presheafOfModules_unitStalkLinearEquiv (Spec (.of L)).presheaf x
    specFieldStalkRingEquivAt x
        (uL.symm (p (schemeModuleStalkLinearMap
          (fieldPointPushforwardScalarEndomorphismAddHom i a) (i x) y))) =
      a * specFieldStalkRingEquivAt x (uL.symm (p y)) := by
  dsimp
  letI : Module (X.presheaf.stalk (i x))
      (((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  letI : Module ((Spec (.of L)).presheaf.stalk x)
      ((show (Spec (.of L)).Modules from
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  let p := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
  let uL := presheafOfModules_unitStalkLinearEquiv (Spec (.of L)).presheaf x
  rw [fieldPointPushforwardScalarEndomorphism_stalk_multiplication]
  rw [map_mul, specFieldStalkRingEquivAt_germ_affineFunctionHom_id]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- On the actual pushed point-sheaf stalk, multiplication by a residue-field
scalar is multiplication by the chosen ambient local-ring lift. -/
theorem fieldPointPushforwardScalarEndomorphism_stalk_eq_smul_lift
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L)) (a : L)
    (y : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :
    letI : Module (X.presheaf.stalk (i x))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    schemeModuleStalkLinearMap
        (fieldPointPushforwardScalarEndomorphismAddHom i a) (i x) y =
      fieldPointScalarLift i x a • y := by
  dsimp
  let P := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  letI : Module (X.presheaf.stalk (i x)) (P.presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  letI : Module ((Spec (.of L)).presheaf.stalk x)
      ((show (Spec (.of L)).Modules from
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  let p := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
  let uL := presheafOfModules_unitStalkLinearEquiv (Spec (.of L)).presheaf x
  let e := specFieldStalkRingEquivAt x
  let coord : P.presheaf.stalk (i x) → L := fun z ↦ e (uL.symm (p z))
  haveI : IsIso p :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat i.isClosedEmbedding.isInducing
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
  have hcoord : Function.Injective coord :=
    e.injective.comp (uL.symm.injective.comp
      (ConcreteCategory.bijective_of_isIso p).injective)
  let q := closedImmersionPushforwardStalkFromRingLinearMap i (i x)
  obtain ⟨s, rfl⟩ :=
    closedImmersionPushforwardStalkFromRingLinearMap_surjective i (i x) y
  apply hcoord
  have hscale := fieldPointPushforwardScalarEndomorphism_stalk_coordinate i x a (q s)
  change coord (schemeModuleStalkLinearMap
      (fieldPointPushforwardScalarEndomorphismAddHom i a) (i x) (q s)) =
    a * coord (q s) at hscale
  rw [hscale]
  rw [← q.map_smul]
  have hq (t : X.presheaf.stalk (i x)) :
      coord (q t) = e (i.stalkMap x t) := by
    exact congrArg e
      (closedImmersionPushforwardStalkFromRingLinearMap_comp_stalkPushforward
        i x t)
  rw [hq, hq]
  rw [smul_eq_mul, map_mul, map_mul]
  have hr : e (i.stalkMap x (fieldPointScalarLift i x a)) = a :=
    (closedFieldPointResidueRingEquivAt_residue_eq_stalkMap
      i x (fieldPointScalarLift i x a)).symm.trans
        (fieldPointScalarLift_residue i x a)
  rw [hr]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- After trivializing the tensor factor, the scalar endomorphism of the
twisted pushed point sheaf is multiplication by `a` in its canonical
`L`-valued stalk coordinate. -/
theorem fieldPointPushforwardTwistScalarEndomorphism_stalk_coordinate
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (T : X.Modules)
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (x : Spec (.of L)) (a : L)
    (y : (schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T).presheaf.stalk (i x)) :
    let P := (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    letI : Module (X.presheaf.stalk (i x))
        ((schemeModuleTensor P T).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module (X.presheaf.stalk (i x)) (P.presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module ((Spec (.of L)).presheaf.stalk x)
        ((show (Spec (.of L)).Modules from
          SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
      schemeModuleStalkModule _ x
    let t := schemeModuleStalkLinearEquivOfIso
      ((schemeModuleTensorRightIsoUnit eT).app P) (i x)
    let p := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
    let uL := presheafOfModules_unitStalkLinearEquiv (Spec (.of L)).presheaf x
    specFieldStalkRingEquivAt x
        (uL.symm (p (t (schemeModuleStalkLinearMap
          (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)
          (i x) y)))) =
      a * specFieldStalkRingEquivAt x (uL.symm (p (t y))) := by
  dsimp
  let P := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  letI : Module (X.presheaf.stalk (i x))
      ((schemeModuleTensor P T).presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  letI : Module (X.presheaf.stalk (i x)) (P.presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  letI : Module ((Spec (.of L)).presheaf.stalk x)
      ((show (Spec (.of L)).Modules from
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.stalk x) :=
    schemeModuleStalkModule _ x
  let s := fieldPointPushforwardScalarEndomorphismAddHom i a
  have ht := schemeModuleStalkLinearEquiv_tensorRightIsoUnit_naturality
    eT s (i x) y
  have hs : fieldPointPushforwardTwistScalarEndomorphismAddHom i T a =
      (schemeModuleTensorRight T).map s := rfl
  rw [hs]
  let p := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).val.presheaf x
  let uL := presheafOfModules_unitStalkLinearEquiv (Spec (.of L)).presheaf x
  let coord : P.presheaf.stalk (i x) → L :=
    fun z ↦ specFieldStalkRingEquivAt x (uL.symm (p z))
  let t : (schemeModuleTensor P T).presheaf.stalk (i x) ≃ₗ[
      X.presheaf.stalk (i x)] P.presheaf.stalk (i x) :=
    schemeModuleStalkLinearEquivOfIso
      ((schemeModuleTensorRightIsoUnit eT).app P) (i x)
  change coord (t (schemeModuleStalkLinearMap
      ((schemeModuleTensorRight T).map s) (i x) y)) = a * coord (t y)
  calc
    coord (t (schemeModuleStalkLinearMap
        ((schemeModuleTensorRight T).map s) (i x) y)) =
        coord (schemeModuleStalkLinearMap s (i x) (t y)) := congrArg coord ht
    _ = a * coord (t y) :=
      fieldPointPushforwardScalarEndomorphism_stalk_coordinate i x a (t y)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- On the actual twisted pushed point-sheaf stalk, the field scalar is the
ambient local-ring action of the chosen lift. -/
theorem fieldPointPushforwardTwistScalarEndomorphism_stalk_eq_smul_lift
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (x : Spec (.of L)) (a : L)
    (y : (schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T).presheaf.stalk (i x)) :
    let P := (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    letI : Module (X.presheaf.stalk (i x))
        ((schemeModuleTensor P T).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module (X.presheaf.stalk (i x)) (P.presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    schemeModuleStalkLinearMap
        (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a) (i x) y =
      fieldPointScalarLift i x a • y := by
  dsimp
  let P := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  letI : Module (X.presheaf.stalk (i x))
      ((schemeModuleTensor P T).presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  letI : Module (X.presheaf.stalk (i x)) (P.presheaf.stalk (i x)) :=
    schemeModuleStalkModule _ (i x)
  let s := fieldPointPushforwardScalarEndomorphismAddHom i a
  let t : (schemeModuleTensor P T).presheaf.stalk (i x) ≃ₗ[
      X.presheaf.stalk (i x)] P.presheaf.stalk (i x) :=
    schemeModuleStalkLinearEquivOfIso
      ((schemeModuleTensorRightIsoUnit eT).app P) (i x)
  have ht := schemeModuleStalkLinearEquiv_tensorRightIsoUnit_naturality
    eT s (i x) y
  have hs : fieldPointPushforwardTwistScalarEndomorphismAddHom i T a =
      (schemeModuleTensorRight T).map s := rfl
  rw [hs]
  apply t.injective
  calc
    t (schemeModuleStalkLinearMap
        ((schemeModuleTensorRight T).map s) (i x) y) =
        schemeModuleStalkLinearMap s (i x) (t y) := ht
    _ = fieldPointScalarLift i x a • t y :=
      fieldPointPushforwardScalarEndomorphism_stalk_eq_smul_lift i x a (t y)
    _ = t (fieldPointScalarLift i x a • y) := (t.map_smul _ _).symm

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- On any open where the tensor factor is trivial, the resulting stalk
isomorphism conjugates the twisted field-scalar endomorphism to the
untwisted one.  This is the local-trivialization replacement for the global
trivialization used above. -/
theorem fieldPointPushforwardTwistScalarEndomorphism_stalk_conjugate_of_localTrivialization
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (T : X.Modules)
    (U : X.Opens) (x : Spec (.of L)) (hxU : i x ∈ U)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (a : L)
    (y : (schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T).presheaf.stalk (i x)) :
    let P := (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    let t := (schemeModuleTensorStalkIsoOfLocalTrivialization
      U (⟨i x, hxU⟩ : U) P T eT).hom
    t (schemeModuleStalkLinearMap
        (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a) (i x) y) =
      schemeModuleStalkLinearMap
        (fieldPointPushforwardScalarEndomorphismAddHom i a) (i x) (t y) := by
  dsimp
  let P := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  let s := fieldPointPushforwardScalarEndomorphismAddHom i a
  have h := schemeModuleTensorStalkIsoOfLocalTrivialization_naturality
    U (⟨i x, hxU⟩ : U) eT s
  have hy := congrArg (fun q ↦ q.hom y) h
  exact hy

set_option linter.style.haveILetI false in
/-- The field scalar acts by its ambient local-ring lift on a twisted point
stalk whenever the twist is trivial on a neighborhood of that point. -/
theorem fieldPointPushforwardTwistScalarEndomorphism_stalk_eq_smul_lift_of_localTrivialization
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (T : X.Modules)
    (U : X.Opens) (x : Spec (.of L)) (hxU : i x ∈ U)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (a : L)
    (y : (schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T).presheaf.stalk (i x)) :
    let P := (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    letI : Module (X.presheaf.stalk (i x))
        ((schemeModuleTensor P T).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ _
    schemeModuleStalkLinearMap
        (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a) (i x) y =
      fieldPointScalarLift i x a • y := by
  dsimp
  let P := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  letI := schemeModuleStalkModule (schemeModuleTensor P T) (i x)
  letI := schemeModuleStalkModule P (i x)
  let t : (schemeModuleTensor P T).presheaf.stalk (i x) ≅
      P.presheaf.stalk (i x) :=
    schemeModuleTensorStalkIsoOfLocalTrivialization U (⟨i x, hxU⟩ : U) P T eT
  apply (ConcreteCategory.bijective_of_isIso t.hom).injective
  calc
    t.hom (schemeModuleStalkLinearMap
        (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a) (i x) y) =
        schemeModuleStalkLinearMap
          (fieldPointPushforwardScalarEndomorphismAddHom i a) (i x) (t.hom y) :=
      fieldPointPushforwardTwistScalarEndomorphism_stalk_conjugate_of_localTrivialization
        i T U x hxU eT a y
    _ = fieldPointScalarLift i x a • t.hom y :=
      fieldPointPushforwardScalarEndomorphism_stalk_eq_smul_lift i x a (t.hom y)
    _ = t.hom (fieldPointScalarLift i x a • y) :=
      (schemeModuleTensorStalkIsoOfLocalTrivialization_smul
        U (⟨i x, hxU⟩ : U) P T eT (fieldPointScalarLift i x a) y).symm

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugating the twisted field-scalar endomorphism by any local
complete-intersection presentation gives scalar multiplication by the
chosen ambient lift. -/
theorem fieldPointPushforwardTwistScalarEndomorphism_conjugateStalk_eq_smul
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (x : Spec (.of L)) (f g : X.presheaf.stalk (i x))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj
        (schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (a : L) :
    qM.inv ≫ (schemeModuleStalkModuleFunctor X (i x)).map
        (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a) ≫ qM.hom =
      fieldPointScalarLift i x a • 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change qM.hom (schemeModuleStalkLinearMap
    (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)
      (i x) (qM.inv y)) = fieldPointScalarLift i x a • y
  rw [fieldPointPushforwardTwistScalarEndomorphism_stalk_eq_smul_lift
    i T eT x a, map_smul, qM.inv_hom_id_apply]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugating the twisted field-scalar endomorphism by any local
complete-intersection presentation gives scalar multiplication by the
chosen ambient lift. -/
theorem fieldPointPushforwardTwistScalarEndomorphism_conjugateStalk_eq_smul_of_localTrivialization
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (U : X.Opens) (x : Spec (.of L)) (hxU : i x ∈ U)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) (f g : X.presheaf.stalk (i x))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj
        (schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (a : L) :
    qM.inv ≫ (schemeModuleStalkModuleFunctor X (i x)).map
        (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a) ≫ qM.hom =
      fieldPointScalarLift i x a • 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change qM.hom (schemeModuleStalkLinearMap
    (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)
      (i x) (qM.inv y)) = fieldPointScalarLift i x a • y
  rw [fieldPointPushforwardTwistScalarEndomorphism_stalk_eq_smul_lift_of_localTrivialization
    i T U x hxU eT a, map_smul, qM.inv_hom_id_apply]

/-- A bijective global-to-stalk comparison and a two-parameter local
complete-intersection presentation give the required `L`-valued pointwise
Ext coordinate. -/
noncomputable def fieldPointExtTwoCoordinateAddEquiv
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hstalk : Function.Bijective
      (schemeModuleStalkModuleExtMap X (i x) M N 2)) :
    Ext.{u} M N 2 ≃+ L :=
  (schemeModuleExtLocalResidueComponentLargeAddEquiv
      (i x) M N f g hf hg hfm hgm qM qN hspan hstalk).trans
    (closedFieldPointResidueRingEquivAt i x).toAddEquiv

/-- The concrete `L`-valued residue map.  Keeping this map separate makes it
possible to prove the pointwise equivalence from explicit global classes,
without first proving surjectivity of the entire global-to-stalk Ext map. -/
noncomputable def fieldPointExtTwoResidueCoordinate
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x))) :
    Ext.{u} M N 2 →+ L :=
  (closedFieldPointResidueRingEquivAt i x).toAddEquiv.toAddMonoidHom.comp
    (schemeModuleExtLocalResidueComponentLarge
      (i x) M N f g hf hg hfm hgm qM qN)

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition by the twisted pushforward of multiplication by `a`
scales the `L`-valued field-point residue coordinate by `a`. -/
theorem fieldPointExtTwoResidueCoordinate_precomp_twistScalar
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (x : Spec (.of L)) (N : X.Modules)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj
        (schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (a : L)
    (z : Ext.{u} (schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) N 2) :
    fieldPointExtTwoResidueCoordinate i x _ N f g hf hg hfm hgm qM qN
        ((Ext.mk₀ (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)).comp
          z (zero_add 2)) =
      a * fieldPointExtTwoResidueCoordinate i x _ N f g hf hg hfm hgm qM qN z := by
  change closedFieldPointResidueRingEquivAt i x
      (schemeModuleExtLocalResidueComponentLarge (i x) _ N f g hf hg hfm hgm qM qN
        ((Ext.mk₀ (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)).comp
          z (zero_add 2))) =
    a * closedFieldPointResidueRingEquivAt i x
      (schemeModuleExtLocalResidueComponentLarge (i x) _ N f g hf hg hfm hgm qM qN z)
  rw [schemeModuleExtLocalResidueComponentLarge_precomp_of_conjugate_eq_smul
    (i x) _ N f g hf hg hfm hgm qM qN
    (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)
    (fieldPointScalarLift i x a)
    (fieldPointPushforwardTwistScalarEndomorphism_conjugateStalk_eq_smul
      i T eT x f g qM a) z]
  change closedFieldPointResidueRingEquivAt i x
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
        (fieldPointScalarLift i x a) *
        schemeModuleExtLocalResidueComponentLarge (i x) _ N f g hf hg hfm hgm qM qN z) = _
  rw [map_mul]
  have ha := fieldPointScalarLift_residue i x a
  change closedFieldPointResidueRingEquivAt i x
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
      (fieldPointScalarLift i x a)) = a at ha
  rw [ha]

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition by the twisted pushforward of multiplication by `a`
scales the `L`-valued field-point residue coordinate by `a`. -/
theorem fieldPointExtTwoResidueCoordinate_precomp_twistScalar_of_localTrivialization
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (U : X.Opens) (x : Spec (.of L)) (hxU : i x ∈ U)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U))) (N : X.Modules)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj
        (schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (a : L)
    (z : Ext.{u} (schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) N 2) :
    fieldPointExtTwoResidueCoordinate i x _ N f g hf hg hfm hgm qM qN
        ((Ext.mk₀ (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)).comp
          z (zero_add 2)) =
      a * fieldPointExtTwoResidueCoordinate i x _ N f g hf hg hfm hgm qM qN z := by
  change closedFieldPointResidueRingEquivAt i x
      (schemeModuleExtLocalResidueComponentLarge (i x) _ N f g hf hg hfm hgm qM qN
        ((Ext.mk₀ (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)).comp
          z (zero_add 2))) =
    a * closedFieldPointResidueRingEquivAt i x
      (schemeModuleExtLocalResidueComponentLarge (i x) _ N f g hf hg hfm hgm qM qN z)
  rw [schemeModuleExtLocalResidueComponentLarge_precomp_of_conjugate_eq_smul
    (i x) _ N f g hf hg hfm hgm qM qN
    (fieldPointPushforwardTwistScalarEndomorphismAddHom i T a)
    (fieldPointScalarLift i x a)
    (fieldPointPushforwardTwistScalarEndomorphism_conjugateStalk_eq_smul_of_localTrivialization
      i T U x hxU eT f g qM a) z]
  change closedFieldPointResidueRingEquivAt i x
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
        (fieldPointScalarLift i x a) *
        schemeModuleExtLocalResidueComponentLarge (i x) _ N f g hf hg hfm hgm qM qN z) = _
  rw [map_mul]
  have ha := fieldPointScalarLift_residue i x a
  change closedFieldPointResidueRingEquivAt i x
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
      (fieldPointScalarLift i x a)) = a at ha
  rw [ha]

/-- The pointwise Ext coordinate only needs injectivity of localization and
surjectivity of the concrete residue coordinate.  This is strictly weaker
than requiring the global-to-stalk Ext map itself to be bijective and is the
form suited to constructing preimages by explicit global Yoneda products. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfResidueSurjective
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hstalk : Function.Injective
      (schemeModuleStalkModuleExtMap X (i x) M N 2))
    (hsurj : Function.Surjective
      (fieldPointExtTwoResidueCoordinate
        i x M N f g hf hg hfm hgm qM qN)) :
    Ext.{u} M N 2 ≃+ L := by
  apply AddEquiv.ofBijective
    (fieldPointExtTwoResidueCoordinate
      i x M N f g hf hg hfm hgm qM qN)
  refine ⟨?_, hsurj⟩
  intro z z' h
  apply schemeModuleExtLocalResidueComponentLarge_injective
    (i x) M N f g hf hg hfm hgm qM qN hspan hstalk
  apply (closedFieldPointResidueRingEquivAt i x).injective
  exact h

/-- A right inverse consisting of explicit global degree-two classes
discharges the residue-surjectivity premise of the preceding constructor. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfResidueSection
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hstalk : Function.Injective
      (schemeModuleStalkModuleExtMap X (i x) M N 2))
    (lift : L →+ Ext.{u} M N 2)
    (hlift : ∀ a,
      fieldPointExtTwoResidueCoordinate
        i x M N f g hf hg hfm hgm qM qN (lift a) = a) :
    Ext.{u} M N 2 ≃+ L :=
  fieldPointExtTwoCoordinateAddEquivOfResidueSurjective
    i x M N f g hf hg hfm hgm qM qN hspan hstalk
      (fun a ↦ ⟨lift a, hlift a⟩)

/-- It is enough to construct one global degree-two class of residue `1`
and an additive scalar action on the point-supported source whose
precomposition scales the residue coordinate.  The resulting precomposed
classes form the explicit additive section required above. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfNormalizedClass
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hstalk : Function.Injective
      (schemeModuleStalkModuleExtMap X (i x) M N 2))
    (scale : L →+ (M ⟶ M))
    (z : Ext.{u} M N 2)
    (hone : fieldPointExtTwoResidueCoordinate
      i x M N f g hf hg hfm hgm qM qN z = 1)
    (hscale : ∀ a,
      fieldPointExtTwoResidueCoordinate
          i x M N f g hf hg hfm hgm qM qN
          ((Ext.mk₀ (scale a)).comp z (zero_add 2)) =
        a * fieldPointExtTwoResidueCoordinate
          i x M N f g hf hg hfm hgm qM qN z) :
    Ext.{u} M N 2 ≃+ L := by
  apply fieldPointExtTwoCoordinateAddEquivOfResidueSection
    i x M N f g hf hg hfm hgm qM qN hspan hstalk
    ((extPrecompFixedClassAddHom M N 2 z).comp scale)
  intro a
  rw [AddMonoidHom.comp_apply, extPrecompFixedClassAddHom_apply, hscale, hone,
    mul_one]

/-- A single class with nonzero residue is enough: precomposition by the
inverse residue scalar first normalizes it to residue `1`. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfNonzeroClass
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hstalk : Function.Injective
      (schemeModuleStalkModuleExtMap X (i x) M N 2))
    (scale : L →+ (M ⟶ M))
    (z : Ext.{u} M N 2)
    (hnonzero : fieldPointExtTwoResidueCoordinate
      i x M N f g hf hg hfm hgm qM qN z ≠ 0)
    (hscale : ∀ a,
      fieldPointExtTwoResidueCoordinate
          i x M N f g hf hg hfm hgm qM qN
          ((Ext.mk₀ (scale a)).comp z (zero_add 2)) =
        a * fieldPointExtTwoResidueCoordinate
          i x M N f g hf hg hfm hgm qM qN z) :
    Ext.{u} M N 2 ≃+ L := by
  let b := fieldPointExtTwoResidueCoordinate
    i x M N f g hf hg hfm hgm qM qN z
  let normalize : L →+ L := {
    toFun a := a * b⁻¹
    map_zero' := zero_mul _
    map_add' a a' := add_mul a a' b⁻¹ }
  apply fieldPointExtTwoCoordinateAddEquivOfResidueSection
    i x M N f g hf hg hfm hgm qM qN hspan hstalk
    ((extPrecompFixedClassAddHom M N 2 z).comp (scale.comp normalize))
  intro a
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    extPrecompFixedClassAddHom_apply, hscale]
  change (a * b⁻¹) * b = a
  rw [mul_assoc, inv_mul_cancel₀]
  · exact mul_one a
  · exact hnonzero

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero global class and injective localization give the field-point
Ext equivalence for a twist trivial near the point. Scalar surjectivity is
proved from the actual twisted field endomorphisms. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfLocalTrivialization
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L)) (T : X.Modules) (U : X.Opens) (hxU : i x ∈ U)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj (schemeModuleTensor ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hstalk : Function.Injective
      (schemeModuleStalkModuleExtMap X (i x) (schemeModuleTensor ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) N 2))
    (z : Ext.{u} (schemeModuleTensor ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) N 2)
    (hz : z ≠ 0) :
    Ext.{u} (schemeModuleTensor ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) N 2 ≃+ L := by
  let M := schemeModuleTensor ((Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T
  have hinj := schemeModuleExtLocalResidueComponentLarge_injective
    (i x) M N f g hf hg hfm hgm qM qN hspan hstalk
  have hn : fieldPointExtTwoResidueCoordinate
      i x M N f g hf hg hfm hgm qM qN z ≠ 0 := by
    intro h
    apply hz
    apply hinj
    apply (closedFieldPointResidueRingEquivAt i x).injective
    change closedFieldPointResidueRingEquivAt i x
      (schemeModuleExtLocalResidueComponentLarge (i x) M N f g hf hg hfm hgm qM qN z) = 0 at h
    simpa only [map_zero] using
      h.trans (map_zero (closedFieldPointResidueRingEquivAt i x)).symm
  exact fieldPointExtTwoCoordinateAddEquivOfNonzeroClass
    i x M N f g hf hg hfm hgm qM qN hspan hstalk
    (fieldPointPushforwardTwistScalarEndomorphismAddHom i T) z hn
    (fun a ↦ fieldPointExtTwoResidueCoordinate_precomp_twistScalar_of_localTrivialization
      i T U x hxU eT N f g hf hg hfm hgm qM qN a z)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- For an actual closed field point, the kernel presentation itself makes
the field-valued residue coordinate injective.  No separate assertion that
the two parameters span the maximal ideal is needed: the closed-point stalk
map has that kernel canonically. -/
theorem fieldPointExtTwoResidueCoordinate_injective_of_kernel
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x))) :
    letI : Module (X.presheaf.stalk (i x))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    ∀ (hkernel : LinearMap.ker
        (closedImmersionPushforwardStalkFromRingLinearMap i (i x)) =
          Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))))
      (hstalk : Function.Injective
        (schemeModuleStalkModuleExtMap X (i x) M N 2)),
      Function.Injective
        (fieldPointExtTwoResidueCoordinate
          i x M N f g hf hg hfm hgm qM qN) := by
  dsimp
  intro hkernel hstalk
  let hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) :=
    hkernel.symm.trans
      (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal i x)
  intro z z' h
  apply schemeModuleExtLocalResidueComponentLarge_injective
    (i x) M N f g hf hg hfm hgm qM qN hspan hstalk
  apply (closedFieldPointResidueRingEquivAt i x).injective
  exact h

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Once the closed-point kernel presentation and injectivity of localization
are known, every nonzero global class has nonzero field-valued residue. -/
theorem fieldPointExtTwoResidueCoordinate_ne_zero_of_kernel
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x))) :
    letI : Module (X.presheaf.stalk (i x))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    ∀ (hkernel : LinearMap.ker
        (closedImmersionPushforwardStalkFromRingLinearMap i (i x)) =
          Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))))
      (hstalk : Function.Injective
        (schemeModuleStalkModuleExtMap X (i x) M N 2))
      (z : Ext.{u} M N 2), z ≠ 0 →
      fieldPointExtTwoResidueCoordinate
        i x M N f g hf hg hfm hgm qM qN z ≠ 0 := by
  dsimp
  intro hkernel hstalk z hz hzero
  apply hz
  apply fieldPointExtTwoResidueCoordinate_injective_of_kernel
    i x M N f g hf hg hfm hgm qM qN hkernel hstalk
  simpa using hzero

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Closed-point specialization of
`fieldPointExtTwoCoordinateAddEquivOfNonzeroClass`.  The defining kernel
equality of the local complete intersection automatically supplies the
maximal-ideal span condition. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfNonzeroClassOfKernel
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x))) :
    letI : Module (X.presheaf.stalk (i x))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    ∀ (hkernel : LinearMap.ker
        (closedImmersionPushforwardStalkFromRingLinearMap i (i x)) =
          Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))))
      (hstalk : Function.Injective
        (schemeModuleStalkModuleExtMap X (i x) M N 2))
      (scale : L →+ (M ⟶ M))
      (z : Ext.{u} M N 2)
      (hnonzero : fieldPointExtTwoResidueCoordinate
        i x M N f g hf hg hfm hgm qM qN z ≠ 0)
      (hscale : ∀ a,
        fieldPointExtTwoResidueCoordinate
            i x M N f g hf hg hfm hgm qM qN
            ((Ext.mk₀ (scale a)).comp z (zero_add 2)) =
          a * fieldPointExtTwoResidueCoordinate
            i x M N f g hf hg hfm hgm qM qN z),
      Ext.{u} M N 2 ≃+ L := by
  dsimp
  intro hkernel hstalk scale z hnonzero hscale
  let hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) :=
    hkernel.symm.trans
      (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal i x)
  exact fieldPointExtTwoCoordinateAddEquivOfNonzeroClass
    i x M N f g hf hg hfm hgm qM qN hspan hstalk scale z hnonzero hscale


set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda product of the closed-immersion ideal sequence with a Serre
extension whose middle stalk is free has nonzero field-point residue.  It
therefore supplies the normalized class needed for the pointwise `Ext²`
coordinate equivalence. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfLocallyFreeSerreYonedaClass
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    {T : X.Modules}
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (eT : T ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    (x : Spec (.of L)) [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))] :
    letI : Module (X.presheaf.stalk (i x))
        ((show X.Modules from e.E).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module (X.presheaf.stalk (i x))
        ((show X.Modules from closedImmersionIdealTwist i T).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module (X.presheaf.stalk (i x))
        ((show X.Modules from IdealSheafDataModule.closedImmersionModule i).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module (X.presheaf.stalk (i x))
        ((show X.Modules from (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : Module (X.presheaf.stalk (i x))
        ((show X.Modules from schemeModuleTensor
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T).presheaf.stalk (i x)) :=
      schemeModuleStalkModule _ (i x)
    letI : (schemeModuleStalkModuleFunctor X (i x)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    ∀ (f g c : X.presheaf.stalk (i x))
      (hkernel : LinearMap.ker
        (closedImmersionPushforwardStalkFromRingLinearMap i (i x)) =
          Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))))
      (e₁ e₂ : ((show X.Modules from e.E).presheaf.stalk (i x)))
      (hq₁ : (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT (i x) f g hkernel)
          (schemeModuleStalkLinearMap e.projection (i x) e₁) =
        ⟨f, Ideal.subset_span (by simp)⟩)
      (hq₂ : (closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
          i eT (i x) f g hkernel)
          (schemeModuleStalkLinearMap e.projection (i x) e₂) =
        ⟨g, Ideal.subset_span (by simp)⟩)
      (hrel : (-g) • e₁ + f • e₂ =
        serreExtensionStalkCanonicalSection e (i x) c)
      (hf : IsRegular f)
      (hg : IsRegular (Ideal.Quotient.mk (Ideal.span {f}) g))
      (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
      (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
      (hfree : Module.Free (X.presheaf.stalk (i x))
        ((show X.Modules from e.E).presheaf.stalk (i x)))
      (hstalk : Function.Injective
        (schemeModuleStalkModuleExtMap X (i x)
          (closedImmersionIdealTwistSequence i T).X₃
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)),
      Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 ≃+ L := by
  dsimp
  intro f g c hkernel e₁ e₂ hq₁ hq₂ hrel hf hg hfm hgm hfree hstalk
  let qI := closedImmersionIdealTwistStalkQuotientLinearEquivOfIsoUnit
    i eT (i x) f g hkernel
  let hpresentation :=
    serreExtension_stalkPresentationEquiv_of_quotientEquiv_of_lifts
      e (i x) f g c qI e₁ e₂ hq₁ hq₂ hrel hf hg
  have hc : IsUnit c :=
    (localSerreExtensionPresentation_free_iff_isUnit_of_sheafStalk
      (show X.Modules from e.E) (i x) f g c
      (isRegular_iff_mem_nonZeroDivisors.mp hf) hfm hgm hpresentation).mp hfree
  let qM := LinearEquiv.toModuleIso
    (closedImmersionPushforwardTwistStalkQuotientLinearEquivOfIsoUnit
      i eT (i x) f g hkernel)
  let qN := schemeModuleUnitStalkIso X (i x)
  let z := (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
    (@SerreExtensionSequenceData.extensionClass.{u} X
      (closedImmersionIdealTwist i T) e hExt)
    (show 1 + 1 = 2 by omega)
  apply fieldPointExtTwoCoordinateAddEquivOfNonzeroClassOfKernel
    i x (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    f g (isRegular_iff_mem_nonZeroDivisors.mp hf)
      (isRegular_iff_mem_nonZeroDivisors.mp hg) hfm hgm qM qN
      hkernel hstalk
      (fieldPointPushforwardTwistScalarEndomorphismAddHom i T) z
  · change closedFieldPointResidueRingEquivAt i x
      (schemeModuleExtLocalResidueComponentLarge (i x) _ _ f g _ _ hfm hgm qM qN z) ≠ 0
    have hcoord :=
      schemeModuleExtLocalResidueComponentLarge_serreYonedaProduct_eq_coordinate
        i eT e (i x) f g c hkernel e₁ e₂ hq₁ hq₂ hrel hf hg hfm hgm
    change schemeModuleExtLocalResidueComponentLarge (i x) _ _ f g _ _ hfm hgm
      qM qN z = Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) c at hcoord
    rw [hcoord]
    apply (map_ne_zero (closedFieldPointResidueRingEquivAt i x)).2
    intro hz
    exact (IsLocalRing.notMem_maximalIdeal.mpr hc)
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  · intro a
    exact fieldPointExtTwoResidueCoordinate_precomp_twistScalar
      i T eT x (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      f g (isRegular_iff_mem_nonZeroDivisors.mp hf)
      (isRegular_iff_mem_nonZeroDivisors.mp hg) hfm hgm qM qN a z

end PfaffianDescent
