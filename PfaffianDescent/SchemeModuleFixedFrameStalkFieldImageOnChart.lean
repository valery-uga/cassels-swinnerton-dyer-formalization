import PfaffianDescent.SchemeModuleFixedFrameFunctionFieldShrinking

/-! Actual fixed-frame stalk image and injectivity at points of the chart.
Original generic germs and actual inverse chart sections prove these facts;
no field image, local freeness or injectivity certificate is assumed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem generic_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

private theorem restrictedChart_coefficient
    (M : X.Modules) (C : X.Opens)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    {U : X.Opens} (f : U ⟶ C) (a : M.val.obj (op U)) :
    SchemeModuleInternalHom.overTopLinearEquiv M U
        (SchemeModuleInternalHom.overUnitChartRestrict M f e) a =
      (e.hom.val.app (op (Over.mk f)) a : Γ(X, U)) := rfl

/-- On ANY actual subopen of its chart, the fixed-complement local map is
literally the original coefficient germ, without shrinking a chosen scalar. -/
theorem schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply_of_le
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (U : X.Opens) [Nonempty U] (f : U ⟶ C) (a : M.val.obj (op U)) :
    (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U a : X.functionField) =
      X.germToFunctionField U (e.hom.val.app (op (Over.mk f)) a) := by
  let W : X.Opens := U ⊓ C
  letI : Nonempty W := ⟨⟨genericPoint X, generic_mem U, generic_mem C⟩⟩
  let r : W ⟶ U := homOfLE inf_le_left
  let g : W ⟶ C := homOfLE inf_le_right
  let k : Over.mk g ⟶ Over.mk f := Over.homMk r (Subsingleton.elim _ _)
  have hc : (e.hom.val.app (op (Over.mk g)) (M.val.map r.op a) : Γ(X, W)) =
      X.presheaf.map r.op (e.hom.val.app (op (Over.mk f)) a) :=
    PresheafOfModules.naturality_apply e.hom.val k.op a
  exact (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C e U a).trans
    ((congrArg (X.germToFunctionField W) hc).trans
      (X.presheaf.germ_res_apply r (genericPoint X) (generic_mem W) _))

/-- At a point of the actual fixed chart, the FULL stalk image is the
native local-ring image in the original function field. Surjectivity onto
that image comes from actual inverse chart sections, not an input. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_range_of_mem
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (x : X) (hxC : x ∈ C) :
    letI := schemeModuleStalkModule M x
    Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x) =
      Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  letI := schemeModuleStalkModule M x
  let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x
  let κ := algebraMap (X.presheaf.stalk x) X.functionField
  apply Set.Subset.antisymm
  · rintro z ⟨a, ha⟩
    obtain ⟨U, hxU, m, hm⟩ := M.presheaf.exists_germ_eq a
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    let W : X.Opens := U ⊓ C
    have hxW : x ∈ W := ⟨hxU, hxC⟩
    letI : Nonempty W := ⟨⟨x, hxW⟩⟩
    let r : W ⟶ U := homOfLE inf_le_left
    let f : W ⟶ C := homOfLE inf_le_right
    let c : Γ(X, W) := e.hom.val.app (op (Over.mk f)) (M.val.map r.op m)
    have hval : ψ a = κ (X.presheaf.germ W x hxW c) :=
      (congrArg ψ hm.symm).trans
        ((schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e x U hxU m).trans
          ((schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi M C e U m).trans
            (Scheme.algebraMap_germ_eq_germToFunctionField X hxW c).symm))
    exact ⟨X.presheaf.germ W x hxW c, hval.symm.trans ha⟩
  · rintro z ⟨r, hr⟩
    obtain ⟨V, hVC, hxV, rV, hV⟩ := X.presheaf.exists_le_germ_eq r hxC
    letI : Nonempty V := ⟨⟨x, hxV⟩⟩
    let f : V ⟶ C := homOfLE hVC
    let q := SchemeModuleInternalHom.overTopLinearEquiv M V
      (SchemeModuleInternalHom.overUnitChartRestrict M f e)
    let m : M.val.obj (op V) := q.symm rV
    have hc : (e.hom.val.app (op (Over.mk f)) m : Γ(X, V)) = rV :=
      (restrictedChart_coefficient M C e f m).symm.trans (q.apply_symm_apply rV)
    refine ⟨M.presheaf.germ V x hxV m, ?_⟩
    exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e x V hxV m).trans
      ((schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply_of_le pi M C e V f m).trans
        ((congrArg (X.germToFunctionField V) hc).trans
          ((Scheme.algebraMap_germ_eq_germToFunctionField X hxV rV).symm.trans
            ((congrArg κ hV).trans hr))))

/-- Genuine stalk injectivity at points of the chart. Common actual
representatives, the original generic-germ injection and the actual
coefficient LinearEquiv prove this without an injectivity premise. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_mem
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (x : X) (hxC : x ∈ C) :
    letI := schemeModuleStalkModule M x
    Function.Injective (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x) := by
  letI := schemeModuleStalkModule M x
  let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x
  intro a b hab
  obtain ⟨U, hxU, m, hm⟩ := M.presheaf.exists_germ_eq a
  obtain ⟨V, hVU, hxV, n, hn⟩ := M.presheaf.exists_le_germ_eq b hxU
  let W : X.Opens := V ⊓ C
  have hxW : x ∈ W := ⟨hxV, hxC⟩
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  let fU : W ⟶ U := homOfLE (inf_le_left.trans hVU)
  let fV : W ⟶ V := homOfLE inf_le_left
  let fC : W ⟶ C := homOfLE inf_le_right
  let mW : M.val.obj (op W) := M.val.map fU.op m
  let nW : M.val.obj (op W) := M.val.map fV.op n
  have haW : M.presheaf.germ W x hxW mW = a :=
    (M.presheaf.germ_res_apply fU x hxW m).trans hm
  have hbW : M.presheaf.germ W x hxW nW = b :=
    (M.presheaf.germ_res_apply fV x hxW n).trans hn
  let q := SchemeModuleInternalHom.overTopLinearEquiv M W
    (SchemeModuleInternalHom.overUnitChartRestrict M fC e)
  have hval (s : M.val.obj (op W)) :
      ψ (M.presheaf.germ W x hxW s) = X.germToFunctionField W (q s) :=
    (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e x W hxW s).trans
      ((schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply_of_le pi M C e W fC s).trans
        (congrArg (X.germToFunctionField W) (restrictedChart_coefficient M C e fC s).symm))
  have hq : q mW = q nW := (X.germToFunctionField_injective W)
    ((hval mW).symm.trans ((congrArg ψ haW).trans
      (hab.trans ((congrArg ψ hbW).symm.trans (hval nW)))))
  exact haW.symm.trans ((congrArg (M.presheaf.germ W x hxW) (q.injective hq)).trans hbW)

end PfaffianDescent
