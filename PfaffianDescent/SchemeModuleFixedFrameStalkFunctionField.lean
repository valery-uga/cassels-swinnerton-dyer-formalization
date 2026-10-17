import PfaffianDescent.SchemeModuleCanonicalChartFunctionField
import PfaffianDescent.VoisinSheafStalk

/-! Actual fixed-frame local maps and their literal stalk descent. The
frame is an actual unit chart on a nonempty open, and restriction/naturality
prove every comparison. Native stalk modules and the original pi/field
scalars are retained; no compatibility or image certificate is supplied.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restrictedChart_coefficient
    (M : X.Modules) (C : X.Opens)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    {W : X.Opens} (f : W ⟶ C) (a : M.val.obj (op W)) :
    SchemeModuleInternalHom.overTopLinearEquiv M W
        (SchemeModuleInternalHom.overUnitChartRestrict M f e) a =
      (e.hom.val.app (op (Over.mk f)) a : Γ(X, W)) := rfl

private theorem frameCoefficient_restrict
    (M : X.Modules) (C : X.Opens)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    {U W : X.Opens} (fU : U ⟶ C) (fW : W ⟶ C) (g : W ⟶ U)
    (a : M.val.obj (op U)) :
    (e.hom.val.app (op (Over.mk fW)) (M.val.map g.op a) : Γ(X, W)) =
      X.presheaf.map g.op (e.hom.val.app (op (Over.mk fU)) a) := by
  let k : Over.mk fW ⟶ Over.mk fU := Over.homMk g (Subsingleton.elim _ _)
  exact PresheafOfModules.naturality_apply e.hom.val k.op a

private theorem additiveRestriction_comp
    {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u})
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D)
    (he : f ≫ g = h) (s : F.obj A) :
    F.map g (F.map f s) = F.map h s :=
  (ConcreteCategory.congr_hom (F.map_comp f g) s).symm.trans
    (congrArg (fun k : A ⟶ D => F.map k s) he)

variable {K : Type u} [Field K] [IsIntegral X]

private theorem generic_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

private def infNonempty (U C : X.Opens) [Nonempty U] [Nonempty C] : Nonempty ↥(U ⊓ C : X.Opens) :=
  ⟨⟨genericPoint X, generic_mem U, generic_mem C⟩⟩

/-- SAME original-pi local section map through the actual restricted
fixed chart on U intersection C. This is a composition of existing actual
section restriction and chart field maps, not a replacement scalar action. -/
def schemeModuleFixedFrameOpenToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (U : X.Opens) [Nonempty U] :
    SchemeModuleOpenSectionsOver pi M U →ₗ[K] SchemeFunctionFieldOver pi := by
  let W := U ⊓ C
  letI : Nonempty W := infNonempty U C
  let eW := SchemeModuleInternalHom.overUnitChartRestrict M
    (homOfLE (show W ≤ C from inf_le_right)) e
  exact (schemeModuleChartSectionsToFunctionFieldLinearMap pi M W eW).comp
    (schemeModuleOpenSectionsRestrictionLinearMap pi M (show W ≤ U from inf_le_left))

/-- The coefficient is the literal ORIGINAL over-site chart component
on the restricted section, at EVERY nonempty local open. -/
theorem schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (U : X.Opens) [Nonempty U] (a : M.val.obj (op U)) :
    let W := U ⊓ C
    letI : Nonempty W := infNonempty U C
    (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U a : X.functionField) =
      X.germToFunctionField W
        (e.hom.val.app (op (Over.mk (homOfLE (show W ≤ C from inf_le_right))))
          (M.val.map (homOfLE (show W ≤ U from inf_le_left)).op a)) := by
  dsimp only
  let W := U ⊓ C
  letI : Nonempty W := infNonempty U C
  change X.germToFunctionField W
      (SchemeModuleInternalHom.overTopLinearEquiv M W
        (SchemeModuleInternalHom.overUnitChartRestrict M (homOfLE inf_le_right) e)
        (M.val.map (homOfLE (show W ≤ U from inf_le_left)).op a)) = _
  exact congrArg (X.germToFunctionField W)
    (restrictedChart_coefficient M C e (homOfLE inf_le_right) _)

/-- Actual fixed-frame maps commute with EVERY original section
restriction. Naturality of the same e proves the comparison internally. -/
theorem schemeModuleFixedFrameOpenToFunctionFieldLinearMap_restrict
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    {U V : X.Opens} [Nonempty U] [Nonempty V] (f : V ⟶ U)
    (a : M.val.obj (op U)) :
    schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e V (M.val.map f.op a) =
      schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U a := by
  let A := U ⊓ C
  let B := V ⊓ C
  letI : Nonempty A := infNonempty U C
  letI : Nonempty B := infNonempty V C
  let g : B ⟶ A := homOfLE (inf_le_inf f.le le_rfl)
  let rU : A ⟶ U := homOfLE inf_le_left
  let rV : B ⟶ V := homOfLE inf_le_left
  let r : B ⟶ U := homOfLE (inf_le_left.trans f.le)
  have hs : M.val.map rV.op (M.val.map f.op a) = M.val.map g.op (M.val.map rU.op a) :=
    (additiveRestriction_comp M.val.presheaf f.op rV.op r.op (Subsingleton.elim _ _) a).trans
      (additiveRestriction_comp M.val.presheaf rU.op g.op r.op (Subsingleton.elim _ _) a).symm
  have hc := frameCoefficient_restrict M C e
    (homOfLE (show A ≤ C from inf_le_right))
    (homOfLE (show B ≤ C from inf_le_right)) g (M.val.map rU.op a)
  exact (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C e V _).trans
    ((congrArg (fun s => X.germToFunctionField B
        (e.hom.val.app (op (Over.mk (homOfLE (show B ≤ C from inf_le_right)))) s)) hs).trans
      ((congrArg (X.germToFunctionField B) hc).trans
        ((X.presheaf.germ_res_apply g (genericPoint X) (generic_mem B) _).trans
          (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C e U a).symm)))

private theorem fixedFrameOpen_smul
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (U : X.Opens) [Nonempty U] (r : Γ(X, U)) (a : M.val.obj (op U)) :
    (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U (r • a) : X.functionField) =
      @HMul.hMul X.functionField X.functionField X.functionField inferInstance
        (X.germToFunctionField U r)
        (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U a) := by
  let W := U ⊓ C
  letI : Nonempty W := infNonempty U C
  let f : W ⟶ U := homOfLE inf_le_left
  let q := SchemeModuleInternalHom.overTopLinearEquiv M W
    (SchemeModuleInternalHom.overUnitChartRestrict M (homOfLE inf_le_right) e)
  have hs : M.val.map f.op (r • a) =
      (X.presheaf.map f.op r : Γ(X, W)) • M.val.map f.op a := M.val.map_smul f.op r a
  change X.germToFunctionField W (q (M.val.map f.op (r • a))) =
    X.germToFunctionField U r * X.germToFunctionField W (q (M.val.map f.op a))
  rw [hs, q.map_smul]
  change X.germToFunctionField W (X.presheaf.map f.op r * q (M.val.map f.op a)) = _
  exact ((X.germToFunctionField W).hom.map_mul _ _).trans
    (congrArg (fun c : X.functionField => c * X.germToFunctionField W (q (M.val.map f.op a)))
      (X.presheaf.germ_res_apply f (genericPoint X) (generic_mem W) r))

private def fixedFrameFieldCocone
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) :=
  { pt := AddCommGrpCat.of X.functionField
    ι :=
      { app := fun A => by
          letI : Nonempty A.unop.1 := ⟨⟨x, A.unop.2⟩⟩
          exact AddCommGrpCat.ofHom
            (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e A.unop.1).toAddMonoidHom
        naturality := by
          intro A B g
          letI : Nonempty A.unop.1 := ⟨⟨x, A.unop.2⟩⟩
          letI : Nonempty B.unop.1 := ⟨⟨x, B.unop.2⟩⟩
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro a
          change schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e B.unop.1
              (M.val.map ((OpenNhds.inclusion x).map g.unop).op a) =
            schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e A.unop.1 a
          exact schemeModuleFixedFrameOpenToFunctionFieldLinearMap_restrict pi M C e
            (U := A.unop.1) (V := B.unop.1) ((OpenNhds.inclusion x).map g.unop) a } }

private def fixedFrameStalkFieldAddHom
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    M.presheaf.stalk x →+ X.functionField :=
  (colimit.desc ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    (fixedFrameFieldCocone pi M C e x)).hom

private theorem fixedFrameStalkFieldAddHom_germ
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X)
    (U : X.Opens) (hxU : x ∈ U) :
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    ∀ a : M.val.obj (op U),
      fixedFrameStalkFieldAddHom pi M C e x (M.presheaf.germ U x hxU a) =
        schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U a := by
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  intro a
  exact DFunLike.congr_fun
    (congrArg (fun k : M.presheaf.obj (op U) ⟶ AddCommGrpCat.of X.functionField => k.hom)
      (colimit.ι_desc (fixedFrameFieldCocone pi M C e x) (op ⟨U, hxU⟩))) a

/-- Actual stalk-to-field map from a fixed actual nonempty chart. The
source has the EXISTING native local-ring action, the target the ORIGINAL
stalk-field algebraMap. All local-map coherence is proved internally. -/
def schemeModuleFixedFrameStalkToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    letI := schemeModuleStalkModule M x
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.functionField := by
  letI := schemeModuleStalkModule M x
  exact
    { toAddHom := (fixedFrameStalkFieldAddHom pi M C e x).toAddHom
      map_smul' := by
        intro r a
        obtain ⟨U, hxU, rU, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hVU, hxV, aV, rfl⟩ := M.presheaf.exists_le_germ_eq a hxU
        letI : Nonempty V := ⟨⟨x, hxV⟩⟩
        let rV : Γ(X, V) := X.presheaf.map (homOfLE hVU).op rU
        let ψ : M.presheaf.stalk x →+ X.functionField := fixedFrameStalkFieldAddHom pi M C e x
        let F : M.val.obj (op V) → X.functionField :=
          schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e V
        let κ := algebraMap (X.presheaf.stalk x) X.functionField
        have hr : X.presheaf.germ V x hxV rV = X.presheaf.germ U x hxU rU :=
          X.presheaf.germ_res_apply (homOfLE hVU) x hxV rU
        have hm : X.presheaf.germ U x hxU rU • M.presheaf.germ V x hxV aV =
            M.presheaf.germ V x hxV (rV • aV) :=
          (congrArg (fun c : X.presheaf.stalk x => c • M.presheaf.germ V x hxV aV) hr).symm.trans
            (PresheafOfModules.germ_smul M.val x V hxV rV aV).symm
        have hψ : ψ (M.presheaf.germ V x hxV aV) = F aV :=
          fixedFrameStalkFieldAddHom_germ pi M C e x V hxV aV
        change ψ (X.presheaf.germ U x hxU rU • M.presheaf.germ V x hxV aV) =
          κ (X.presheaf.germ U x hxU rU) * ψ (M.presheaf.germ V x hxV aV)
        calc
          _ = ψ (M.presheaf.germ V x hxV (rV • aV)) := congrArg ψ hm
          _ = F (rV • aV) := fixedFrameStalkFieldAddHom_germ pi M C e x V hxV (rV • aV)
          _ = X.germToFunctionField V rV * F aV := fixedFrameOpen_smul pi M C e V rV aV
          _ = κ (X.presheaf.germ U x hxU rU) * F aV :=
            congrArg (fun c : X.functionField => c * F aV)
              ((Scheme.algebraMap_germ_eq_germToFunctionField X hxV rV).symm.trans
                (congrArg κ hr))
          _ = _ := congrArg (fun c : X.functionField =>
            κ (X.presheaf.germ U x hxU rU) * c) hψ.symm }

/-- Every local germ is sent through the SAME fixed-complement local
map. No stalk-field comparison premise is used. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X)
    (U : X.Opens) (hxU : x ∈ U) :
    letI := schemeModuleStalkModule M x
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    ∀ a : M.val.obj (op U),
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x
          (M.presheaf.germ U x hxU a) =
        schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U a := by
  letI := schemeModuleStalkModule M x
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  intro a
  exact fixedFrameStalkFieldAddHom_germ pi M C e x U hxU a

private theorem fixedFrameOpen_restrict_global
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (U : X.Opens) [Nonempty U] (a : M.val.obj (op ⊤)) :
    schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U
        (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op a) =
      schemeModuleTopSectionsToFunctionFieldLinearMap pi M C (generic_mem C) e a := by
  let W := U ⊓ C
  letI : Nonempty W := infNonempty U C
  let g : W ⟶ U := homOfLE inf_le_left
  let f : W ⟶ C := homOfLE inf_le_right
  let aC := M.val.map (homOfLE (show C ≤ ⊤ from le_top)).op a
  have hs : M.val.map g.op (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op a) =
      M.val.map f.op aC :=
    (additiveRestriction_comp M.val.presheaf
      (homOfLE (show U ≤ ⊤ from le_top)).op g.op
      (homOfLE (show W ≤ ⊤ from le_top)).op (Subsingleton.elim _ _) a).trans
        (additiveRestriction_comp M.val.presheaf
          (homOfLE (show C ≤ ⊤ from le_top)).op f.op
          (homOfLE (show W ≤ ⊤ from le_top)).op (Subsingleton.elim _ _) a).symm
  have hc := frameCoefficient_restrict M C e (𝟙 C) f f aC
  have h := (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C e U _).trans
    ((congrArg (fun s => X.germToFunctionField W (e.hom.val.app (op (Over.mk f)) s)) hs).trans
      ((congrArg (X.germToFunctionField W) hc).trans
        (X.presheaf.germ_res_apply f (genericPoint X) (generic_mem W) _)))
  exact h

/-- Agreement with the ORIGINAL existing global section-to-field map.
Fixed-frame descent does not rename an unrelated rational comparison. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_global_germ
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    letI := schemeModuleStalkModule M x
    ∀ a : SchemeModuleOpenSectionsOver pi M ⊤,
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x
          (M.presheaf.germ ⊤ x trivial a) =
        schemeModuleTopSectionsToFunctionFieldLinearMap pi M C (generic_mem C) e a := by
  letI := schemeModuleStalkModule M x
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  intro a
  have hid : M.val.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op a = a :=
    ConcreteCategory.congr_hom (M.val.presheaf.map_id (op ⊤)) a
  exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e x ⊤ trivial a).trans
    ((congrArg (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e ⊤) hid).symm.trans
      (fixedFrameOpen_restrict_global pi M C e ⊤ a))

end PfaffianDescent
