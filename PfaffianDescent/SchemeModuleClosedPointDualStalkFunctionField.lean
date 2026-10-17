import PfaffianDescent.SchemeModuleClosedPointDualFractionFormula
import PfaffianDescent.VoisinSheafStalk

/-! The literal dual-presheaf stalk mapped canonically into the original
function field. Actual punctured-open frames give restriction compatibility;
the actual stalk colimit constructs the map. Native stalk scalar action and
rank-one geometry prove linearity/injectivity, rather than certificates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalFrame_inclusion
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (closedImmersionModuleToUnit i).val.app (op U)
      ((schemeModuleClosedPointIdealOverCanonicalIso P U hPU).inv.val.app
        (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = (1 : Γ(X, U)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let e := schemeModuleClosedPointIdealOverCanonicalIso P U hPU
  let T := op (Over.mk (𝟙 U))
  have h := (SchemeModuleInternalHom.overTopLinearEquiv
    (closedImmersionModule i) U e).apply_symm_apply (1 : Γ(X, U))
  change (closedImmersionModuleToUnit i).val.app (op U)
    (e.inv.val.app T (1 : Γ(X, U))) = (1 : Γ(X, U)) at h
  exact h

private theorem originalFrame_restrict
    (P : closedPoints X) {U W : X.Opens} (f : W ⟶ U)
    (hPU : P.1 ∉ U) (hPW : P.1 ∉ W) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    M.val.map f.op
      ((schemeModuleClosedPointIdealOverCanonicalIso P U hPU).inv.val.app
        (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) =
      (schemeModuleClosedPointIdealOverCanonicalIso P W hPW).inv.val.app
        (op (Over.mk (𝟙 W))) (1 : Γ(X, W)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let j := closedImmersionModuleToUnit i
  letI : Mono j := by
    change Mono (idealModuleToUnit i.ker)
    infer_instance
  apply SchemeModuleInternalHom.inclusion_app_injective j W
  exact (PresheafOfModules.naturality_apply j.val f.op _).trans
    ((congrArg (X.presheaf.map f.op) (originalFrame_inclusion P U hPU)).trans
      ((X.presheaf.map f.op).hom.map_one.trans (originalFrame_inclusion P W hPW).symm))

private theorem originalDualChart_apply
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∀ a : (SchemeModuleInternalHom.dual M).val.obj (op U),
      SchemeModuleInternalHom.overTopLinearEquiv (SchemeModuleInternalHom.dual M) U
        (schemeModuleClosedPointDualOverCanonicalIso P U hPU) a =
      (SchemeModuleInternalHom.evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U
        ((schemeModuleClosedPointIdealOverCanonicalIso P U hPU).inv.val.app
          (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) a : Γ(X, U)) := by
  dsimp only
  intro a
  change (schemeModuleClosedPointDualOverCanonicalIso P U hPU).hom.val.app
    (op (Over.mk (𝟙 U))) a = _
  rw [schemeModuleClosedPointDualOverCanonicalIso_hom_val]
  rfl

private theorem originalDualChart_restrict
    (P : closedPoints X) {U W : X.Opens} (f : W ⟶ U)
    (hPU : P.1 ∉ U) (hPW : P.1 ∉ W) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    ∀ a : D.val.obj (op U),
      SchemeModuleInternalHom.overTopLinearEquiv D W
        (schemeModuleClosedPointDualOverCanonicalIso P W hPW) (D.val.map f.op a) =
      X.presheaf.map f.op (SchemeModuleInternalHom.overTopLinearEquiv D U
        (schemeModuleClosedPointDualOverCanonicalIso P U hPU) a) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let D := SchemeModuleInternalHom.dual M
  let bU := (schemeModuleClosedPointIdealOverCanonicalIso P U hPU).inv.val.app
    (op (Over.mk (𝟙 U))) (1 : Γ(X, U))
  let bW := (schemeModuleClosedPointIdealOverCanonicalIso P W hPW).inv.val.app
    (op (Over.mk (𝟙 W))) (1 : Γ(X, W))
  intro a
  have hb : M.val.map f.op bU = bW := originalFrame_restrict P f hPU hPW
  have he : (SchemeModuleInternalHom.evaluationBilinear M O W bW
      (D.val.map f.op a) : Γ(X, W)) =
      X.presheaf.map f.op (SchemeModuleInternalHom.evaluationBilinear M O U bU a) :=
    (congrArg (fun m => SchemeModuleInternalHom.evaluationBilinear M O W m
      (D.val.map f.op a)) hb).symm.trans
        (SchemeModuleInternalHom.evaluationBilinear_restrict M O f bU a).symm
  exact (originalDualChart_apply P W hPW (D.val.map f.op a)).trans
    (he.trans (congrArg (X.presheaf.map f.op) (originalDualChart_apply P U hPU a).symm))

private theorem additiveRestrictions_comp
    {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u})
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D)
    (he : f ≫ g = h) (s : F.obj A) :
    F.map g (F.map f s) = F.map h s := by
  exact (ConcreteCategory.congr_hom (F.map_comp f g) s).symm.trans
    (congrArg (fun k : A ⟶ D => F.map k s) he)

variable {K : Type u} [Field K] [IsIntegral X]

private theorem dualOpenField_restrict
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) {U V : X.Opens} [Nonempty U] [Nonempty V]
    (f : V ⟶ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    ∀ a : D.val.obj (op U),
      schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP V (D.val.map f.op a) =
      schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U a := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  let A := U ⊓ schemeClosedPointComplementOpen P
  let B := V ⊓ schemeClosedPointComplementOpen P
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using (inferInstance : Nonempty V))
  have hgA : genericPoint X ∈ A := ⟨hgU, schemeClosedPoint_generic_mem_complement P hP⟩
  have hgB : genericPoint X ∈ B := ⟨hgV, schemeClosedPoint_generic_mem_complement P hP⟩
  letI : Nonempty A := ⟨⟨genericPoint X, hgA⟩⟩
  letI : Nonempty B := ⟨⟨genericPoint X, hgB⟩⟩
  have hPA : P.1 ∉ A := fun h => schemeClosedPoint_not_mem_complement P h.2
  have hPB : P.1 ∉ B := fun h => schemeClosedPoint_not_mem_complement P h.2
  let g : B ⟶ A := homOfLE (inf_le_inf f.le le_rfl)
  let rU : A ⟶ U := homOfLE inf_le_left
  let rV : B ⟶ V := homOfLE inf_le_left
  let r : B ⟶ U := homOfLE (inf_le_left.trans f.le)
  let qA := SchemeModuleInternalHom.overTopLinearEquiv D A
    (schemeModuleClosedPointDualOverCanonicalIso P A hPA)
  let qB := SchemeModuleInternalHom.overTopLinearEquiv D B
    (schemeModuleClosedPointDualOverCanonicalIso P B hPB)
  intro a
  have hs : D.val.map rV.op (D.val.map f.op a) =
      D.val.map g.op (D.val.map rU.op a) :=
    (additiveRestrictions_comp D.val.presheaf f.op rV.op r.op (Subsingleton.elim _ _) a).trans
      (additiveRestrictions_comp D.val.presheaf rU.op g.op r.op
        (Subsingleton.elim _ _) a).symm
  have hc : qB (D.val.map g.op (D.val.map rU.op a)) =
      X.presheaf.map g.op (qA (D.val.map rU.op a)) :=
    originalDualChart_restrict P g hPA hPB (D.val.map rU.op a)
  change X.germToFunctionField B (qB (D.val.map rV.op (D.val.map f.op a))) =
    X.germToFunctionField A (qA (D.val.map rU.op a))
  exact (congrArg (fun s => X.germToFunctionField B (qB s)) hs).trans
    ((congrArg (X.germToFunctionField B) hc).trans
      (X.presheaf.germ_res_apply g (genericPoint X) hgB (qA (D.val.map rU.op a))))

private theorem dualOpenField_smul
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (U : X.Opens) [Nonempty U] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    ∀ (r : Γ(X, U)) (a : D.val.obj (op U)),
      (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U (r • a) :
        X.functionField) =
      @HMul.hMul X.functionField X.functionField X.functionField inferInstance
        (X.germToFunctionField U r)
        (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U a) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  let W := U ⊓ schemeClosedPointComplementOpen P
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))
  have hgW : genericPoint X ∈ W := ⟨hgU, schemeClosedPoint_generic_mem_complement P hP⟩
  letI : Nonempty W := ⟨⟨genericPoint X, hgW⟩⟩
  have hPW : P.1 ∉ W := fun h => schemeClosedPoint_not_mem_complement P h.2
  let f : W ⟶ U := homOfLE inf_le_left
  let q := SchemeModuleInternalHom.overTopLinearEquiv D W
    (schemeModuleClosedPointDualOverCanonicalIso P W hPW)
  intro r a
  have hs : D.val.map f.op (r • a) =
      (X.presheaf.map f.op r : Γ(X, W)) • D.val.map f.op a := D.val.map_smul f.op r a
  change X.germToFunctionField W (q (D.val.map f.op (r • a))) =
    X.germToFunctionField U r * X.germToFunctionField W (q (D.val.map f.op a))
  rw [hs, q.map_smul]
  change X.germToFunctionField W (X.presheaf.map f.op r * q (D.val.map f.op a)) = _
  exact ((X.germToFunctionField W).hom.map_mul _ _).trans
    (congrArg (fun c : X.functionField => c * X.germToFunctionField W (q (D.val.map f.op a)))
      (X.presheaf.germ_res_apply f (genericPoint X) hgW r))

private def dualFieldCocone
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    Cocone ((OpenNhds.inclusion P.1).op ⋙ D.presheaf) := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  exact
    { pt := AddCommGrpCat.of X.functionField
      ι :=
        { app := fun A => by
            letI : Nonempty A.unop.1 := ⟨⟨P.1, A.unop.2⟩⟩
            exact AddCommGrpCat.ofHom
              (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP A.unop.1).toAddMonoidHom
          naturality := by
            intro A B g
            letI : Nonempty A.unop.1 := ⟨⟨P.1, A.unop.2⟩⟩
            letI : Nonempty B.unop.1 := ⟨⟨P.1, B.unop.2⟩⟩
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro a
            change schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP B.unop.1
                (D.val.map ((OpenNhds.inclusion P.1).map g.unop).op a) =
              schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP A.unop.1 a
            exact dualOpenField_restrict pi P hP (U := A.unop.1) (V := B.unop.1)
              ((OpenNhds.inclusion P.1).map g.unop) a } }

private def dualStalkFieldAddHom
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    D.presheaf.stalk P.1 →+ X.functionField := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  exact (colimit.desc ((OpenNhds.inclusion P.1).op ⋙ D.presheaf)
    (dualFieldCocone pi P hP)).hom

private theorem dualStalkFieldAddHom_germ
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    ∀ (U : X.Opens) (hPU : P.1 ∈ U),
      letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
      ∀ a : D.val.obj (op U),
        dualStalkFieldAddHom pi P hP (D.presheaf.germ U P.1 hPU a) =
          schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U a := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  intro U hPU
  letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
  intro a
  exact DFunLike.congr_fun
    (congrArg (fun k : D.presheaf.obj (op U) ⟶ AddCommGrpCat.of X.functionField => k.hom)
      (colimit.ι_desc (dualFieldCocone pi P hP) (op ⟨U, hPU⟩))) a

/-- Canonical map of the LITERAL actual dual stalk into the ORIGINAL field.
It is the actual colimit descent of the existing local field maps, linear
for the native local-ring action and the original stalk-field algebraMap. -/
def schemeModuleClosedPointDualStalkToFunctionFieldLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    letI := schemeModuleStalkModule D P.1
    D.presheaf.stalk P.1 →ₗ[X.presheaf.stalk P.1] X.functionField := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  letI := schemeModuleStalkModule D P.1
  exact
    { toAddHom := (dualStalkFieldAddHom pi P hP).toAddHom
      map_smul' := by
        intro r a
        obtain ⟨U, hPU, rU, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hVU, hPV, aV, rfl⟩ := D.presheaf.exists_le_germ_eq a hPU
        letI : Nonempty V := ⟨⟨P.1, hPV⟩⟩
        let rV : Γ(X, V) := X.presheaf.map (homOfLE hVU).op rU
        let ψ : D.presheaf.stalk P.1 →+ X.functionField := dualStalkFieldAddHom pi P hP
        let F : D.val.obj (op V) → X.functionField :=
          schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP V
        let κ := algebraMap (X.presheaf.stalk P.1) X.functionField
        have hr : X.presheaf.germ V P.1 hPV rV = X.presheaf.germ U P.1 hPU rU :=
          X.presheaf.germ_res_apply (homOfLE hVU) P.1 hPV rU
        have hm : X.presheaf.germ U P.1 hPU rU • D.presheaf.germ V P.1 hPV aV =
            D.presheaf.germ V P.1 hPV (rV • aV) :=
          (congrArg (fun c : X.presheaf.stalk P.1 =>
            c • D.presheaf.germ V P.1 hPV aV) hr).symm.trans
              (PresheafOfModules.germ_smul D.val P.1 V hPV rV aV).symm
        have hψ : ψ (D.presheaf.germ V P.1 hPV aV) = F aV :=
          dualStalkFieldAddHom_germ pi P hP V hPV aV
        change ψ (X.presheaf.germ U P.1 hPU rU • D.presheaf.germ V P.1 hPV aV) =
          κ (X.presheaf.germ U P.1 hPU rU) * ψ (D.presheaf.germ V P.1 hPV aV)
        calc
          _ = ψ (D.presheaf.germ V P.1 hPV (rV • aV)) := congrArg ψ hm
          _ = F (rV • aV) := dualStalkFieldAddHom_germ pi P hP V hPV (rV • aV)
          _ = X.germToFunctionField V rV * F aV := dualOpenField_smul pi P hP V rV aV
          _ = κ (X.presheaf.germ U P.1 hPU rU) * F aV :=
            congrArg (fun c : X.functionField => c * F aV)
              ((Scheme.algebraMap_germ_eq_germToFunctionField X hPV rV).symm.trans
                (congrArg κ hr))
          _ = _ := congrArg (fun c : X.functionField =>
            κ (X.presheaf.germ U P.1 hPU rU) * c) hψ.symm }

/-- The actual stalk map agrees with the SAME local map on EVERY local
germ representative, not only global sections or one chosen chart. -/
theorem schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_germ
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    letI := schemeModuleStalkModule D P.1
    ∀ (U : X.Opens) (hPU : P.1 ∈ U),
      letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
      ∀ a : D.val.obj (op U),
        schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP
          (D.presheaf.germ U P.1 hPU a) =
          schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U a := by
  dsimp only
  intro U hPU
  letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
  intro a
  exact dualStalkFieldAddHom_germ pi P hP U hPU a

/-- Actual local-germ fraction formula in the ORIGINAL local-ring/field
algebra. The numerator is evaluation on m and the denominator is the
SAME ideal inclusion. Nonvanishing here is an ordinary local-frame input;
the primitive regular-generator source already derives it geometrically. -/
theorem schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_germ_eq_fraction
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    letI := schemeModuleStalkModule D P.1
    ∀ (U : X.Opens) (hPU : P.1 ∈ U),
      letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
      ∀ (m : M.val.obj (op U))
        (hz : ((closedImmersionModuleToUnit i).val.app (op U) m : Γ(X, U)) ≠ 0)
        (a : D.val.obj (op U)),
        schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP
          (D.presheaf.germ U P.1 hPU a) =
          algebraMap (X.presheaf.stalk P.1) X.functionField
            (X.presheaf.germ U P.1 hPU
              (SchemeModuleInternalHom.evaluationBilinear M
                (SheafOfModules.unit X.ringCatSheaf) U m a)) /
          algebraMap (X.presheaf.stalk P.1) X.functionField
            (X.presheaf.germ U P.1 hPU ((closedImmersionModuleToUnit i).val.app (op U) m)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  intro U hPU
  letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
  intro m hz a
  exact (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_germ pi P hP U hPU a).trans
    ((schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_eq_fraction
      pi P hP U m hz a).trans
      (congrArg₂ (fun r s : X.functionField => r / s)
        (Scheme.algebraMap_germ_eq_germToFunctionField X hPU
          (SchemeModuleInternalHom.evaluationBilinear M
            (SheafOfModules.unit X.ringCatSheaf) U m a)).symm
        (Scheme.algebraMap_germ_eq_germToFunctionField X hPU
          ((closedImmersionModuleToUnit i).val.app (op U) m)).symm))

private theorem dualOpenField_injective_of_chart
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (U : X.Opens) [Nonempty U] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∀ e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U,
      Function.Injective (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  intro e a b hab
  change (SchemeModuleInternalHom.dual M).val.obj (op U) at a b
  let m := (SchemeModuleInternalHom.overTopLinearEquiv M U e).symm (1 : Γ(X, U))
  apply (SchemeModuleInternalHom.dualCoefficientLinearEquiv U e).injective
  apply X.germToFunctionField_injective U
  exact (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_mul_frame pi P hP U m a).symm.trans
    ((congrArg (fun t : X.functionField =>
      t * X.germToFunctionField U ((closedImmersionModuleToUnit i).val.app (op U) m)) hab).trans
      (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_mul_frame pi P hP U m b))

/-- Actual rank-one geometry detects zero germs in the canonical stalk map.
The input is genuine unit-chart geometry of the SAME ideal, not desired
restriction injectivity, stalk image, or rational-comparison data. -/
theorem schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_injective
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X)
    (hM : let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i)) :
    Function.Injective (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP) := by
  dsimp only at hM ⊢
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let D := SchemeModuleInternalHom.dual M
  letI := schemeModuleStalkModule D P.1
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨V, hPV, ⟨e⟩⟩ := hM P.1
  obtain ⟨U, hUV, hPU, aU, hUa⟩ := D.presheaf.exists_le_germ_eq a hPV
  letI : Nonempty U := ⟨⟨P.1, hPU⟩⟩
  let eU := SchemeModuleInternalHom.overUnitChartRestrict M (homOfLE hUV) e
  have hzero : (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U aU :
      X.functionField) = 0 :=
    (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_germ pi P hP U hPU aU).symm.trans
      ((congrArg (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP) hUa).trans ha)
  have haU : aU = 0 := dualOpenField_injective_of_chart pi P hP U eU
    (hzero.trans (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP U).map_zero.symm)
  exact hUa.symm.trans ((congrArg (D.presheaf.germ U P.1 hPU) haU).trans
    (D.presheaf.germ U P.1 hPU).hom.map_zero)

end PfaffianDescent
