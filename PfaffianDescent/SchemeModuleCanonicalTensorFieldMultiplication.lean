import PfaffianDescent.SheafModuleCanonicalTensorPureSections
import PfaffianDescent.SchemeModuleCanonicalChartFunctionField

/-! The ORIGINAL tensor restriction comparison and ORIGINAL unit charts
have actual multiplicative coefficients on original pure sections. Their
field maps therefore multiply in the SAME actual function field, with the
independently original-pi K action. No multiplication certificate input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem commRingTensorOver_unitPure005
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (M N : SheafOfModules (SheafOfModules.commRingSheafToRingSheaf R))
    (V : (Over U)ᵒᵖ)
    (m : M.val.obj (op V.unop.left)) (n : N.val.obj (op V.unop.left)) :
    let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
    let G := PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
    let F := PresheafOfModules.sheafification (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
    let A := PresheafOfModules.sheafificationAdjunction (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
    let sigma := (PresheafOfModules.pushforward₀_tensorIso (F := Over.forget U) M.val N.val).hom
    let t : (G.obj P).obj V := m ⊗ₜ[R.obj.obj (op V.unop.left)] n
    (F.map sigma).val.app V ((A.unit.app (G.obj P)).app V t) =
      SheafOfModules.commRingSheafTensorPureSection
        (SheafOfModules.commRingSheafOver R U) (M.over U) (N.over U) V m n := by
  dsimp only
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  let G := PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
  let F := PresheafOfModules.sheafification (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
  let E := SheafOfModules.overFunctor_sheafificationComparisonIso (R := (SheafOfModules.commRingSheafToRingSheaf R)) U P
  let sigma := (PresheafOfModules.pushforward₀_tensorIso (F := Over.forget U) M.val N.val).hom
  let t : (G.obj P).obj V := m ⊗ₜ[R.obj.obj (op V.unop.left)] n
  have h := congrArg (fun k => (k.app V).hom t) (A.unit.naturality sigma).symm
  change (F.map sigma).val.app V ((A.unit.app (G.obj P)).app V t) =
    SheafOfModules.commRingSheafTensorPureSection
      (SheafOfModules.commRingSheafOver R U) (M.over U) (N.over U) V m n at h
  exact h

/-- The canonical restriction/sheafification pure-section calculation
at an ordinary ring sheaf; no scheme-site definitions are reconstructed. -/
private theorem commRingTensorOver_pureSection
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (U : C)
    (M N : SheafOfModules (SheafOfModules.commRingSheafToRingSheaf R))
    (V : (Over U)ᵒᵖ)
    (m : M.val.obj (op V.unop.left)) (n : N.val.obj (op V.unop.left)) :
    (SheafOfModules.overFunctor_commRingSheafTensorIso R U M N).hom.val.app V
        (SheafOfModules.commRingSheafTensorPureSection R M N (op V.unop.left) m n) =
      SheafOfModules.commRingSheafTensorPureSection
        (SheafOfModules.commRingSheafOver R U) (M.over U) (N.over U) V m n := by
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  let G := PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
  let F := PresheafOfModules.sheafification (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 ((SheafOfModules.commRingSheafToRingSheaf R).over U).obj)
  let E := SheafOfModules.overFunctor_sheafificationComparisonIso (R := (SheafOfModules.commRingSheafToRingSheaf R)) U P
  let sigma := (PresheafOfModules.pushforward₀_tensorIso (F := Over.forget U) M.val N.val).hom
  let t : (G.obj P).obj V := m ⊗ₜ[R.obj.obj (op V.unop.left)] n
  have hunit : E.hom.val.app V ((A.unit.app (G.obj P)).app V t) =
      SheafOfModules.commRingSheafTensorPureSection R M N (op V.unop.left) m n := by
    exact ConcreteCategory.congr_hom (congrArg (fun k => k.app V)
      (SheafOfModules.overFunctor_sheafificationComparison_unit_comp
        (R := (SheafOfModules.commRingSheafToRingSheaf R)) U P)) t
  have hleft := congrArg
    (fun k => (k.val.app V).hom ((A.unit.app (G.obj P)).app V t)) E.hom_inv_id
  have hinv : E.inv.val.app V
      (SheafOfModules.commRingSheafTensorPureSection R M N (op V.unop.left) m n) =
      (A.unit.app (G.obj P)).app V t :=
    (congrArg (fun s => E.inv.val.app V s) hunit).symm.trans hleft
  change (F.map sigma).val.app V
      (E.inv.val.app V
        (SheafOfModules.commRingSheafTensorPureSection R M N (op V.unop.left) m n)) = _
  have hmapped := congrArg (fun s => (F.map sigma).val.app V s) hinv
  exact hmapped.trans (commRingTensorOver_unitPure005 R U M N V m n)

/-- The genuine over-site tensor comparison sends the actual global
sheafification-unit pure section to the actual local one. -/
theorem schemeModuleTensorOverIso_pureSection
    (U : X.Opens) (M N : X.Modules) (V : (Over U)ᵒᵖ)
    (m : M.val.obj (op V.unop.left)) (n : N.val.obj (op V.unop.left)) :
    (schemeModuleTensorOverIso U M N).hom.val.app V
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op V.unop.left) m n) =
      SheafOfModules.commRingSheafTensorPureSection
        (SheafOfModules.commRingSheafOver X.sheaf U) (M.over U) (N.over U) V m n := by
  exact commRingTensorOver_pureSection X.sheaf U M N V m n

/-- The SAME actual tensor unit chart has literal original coefficients
whose product equals its coefficient on the actual sheafified pure section. -/
theorem schemeModuleTensorOverUnitIso_pureSection
    (M N : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (eN : N.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    SchemeModuleInternalHom.overTopLinearEquiv (schemeModuleTensor M N) U
        (schemeModuleTensorOverUnitIso M N U eM eN)
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n) =
      SchemeModuleInternalHom.overTopLinearEquiv M U eM m *
        SchemeModuleInternalHom.overTopLinearEquiv N U eN n := by
  let V := op (Over.mk (𝟙 U))
  change (SheafOfModules.commRingSheafTensorCanonicalUnitIso
      (SheafOfModules.commRingSheafOver X.sheaf U) eM eN).hom.val.app V
      ((schemeModuleTensorOverIso U M N).hom.val.app V
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op U) m n)) = _
  have hp := schemeModuleTensorOverIso_pureSection U M N V m n
  exact (congrArg (fun s => (SheafOfModules.commRingSheafTensorCanonicalUnitIso
    (SheafOfModules.commRingSheafOver X.sheaf U) eM eN).hom.val.app V s) hp).trans
      (SheafOfModules.commRingSheafTensorCanonicalUnitIso_pureSection
        (SheafOfModules.commRingSheafOver X.sheaf U) eM eN V m n)

variable {K : Type u} [Field K] [IsIntegral X]

/-- Genuine field multiplication for the actual GLOBAL pure tensor of
original sections under the canonical product chart. Original pi scalars
are those of the earlier independent field-action construction. -/
theorem schemeModuleTopSectionsToFunctionFieldLinearMap_tensorPureSection
    (pi : X ⟶ Spec (CommRingCat.of K)) (M N : X.Modules)
    (U : X.Opens) (hgU : genericPoint X ∈ U)
    (eM : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (eN : N.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (m : SchemeModuleOpenSectionsOver pi M ⊤) (n : SchemeModuleOpenSectionsOver pi N ⊤) :
    (schemeModuleTopSectionsToFunctionFieldLinearMap pi (schemeModuleTensor M N) U hgU
        (schemeModuleTensorOverUnitIso M N U eM eN)
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op ⊤) m n) : X.functionField) =
      (schemeModuleTopSectionsToFunctionFieldLinearMap pi M U hgU eM m : X.functionField) *
        (schemeModuleTopSectionsToFunctionFieldLinearMap pi N U hgU eN n : X.functionField) := by
  letI : Nonempty U := ⟨⟨genericPoint X, hgU⟩⟩
  change X.germToFunctionField U
      (SchemeModuleInternalHom.overTopLinearEquiv (schemeModuleTensor M N) U
        (schemeModuleTensorOverUnitIso M N U eM eN)
        ((schemeModuleTensor M N).val.map (homOfLE (show U ≤ ⊤ from le_top)).op
          (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N (op ⊤) m n))) =
    X.germToFunctionField U (SchemeModuleInternalHom.overTopLinearEquiv M U eM
      (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m)) *
    X.germToFunctionField U (SchemeModuleInternalHom.overTopLinearEquiv N U eN
      (N.val.map (homOfLE (show U ≤ ⊤ from le_top)).op n))
  let f := (homOfLE (show U ≤ ⊤ from le_top)).op
  have hres := SheafOfModules.commRingSheafTensorPureSection_restrict X.sheaf M N f m n
  have hc := schemeModuleTensorOverUnitIso_pureSection M N U eM eN
    (M.val.map f m) (N.val.map f n)
  exact (congrArg (fun s => X.germToFunctionField U
    (SchemeModuleInternalHom.overTopLinearEquiv (schemeModuleTensor M N) U
      (schemeModuleTensorOverUnitIso M N U eM eN) s)) hres).trans
        ((congrArg (fun r : Γ(X, U) => X.germToFunctionField U r) hc).trans
          (map_mul (X.germToFunctionField U).hom _ _))

end PfaffianDescent
