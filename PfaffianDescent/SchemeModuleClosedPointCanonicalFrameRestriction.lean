import PfaffianDescent.SchemeModuleClosedPointCanonicalOpenFrame

/-! Actual point-factor charts restrict to the SAME canonical charts.
The ideal comparison is naturality of the original inclusion; the dual
comparison is literal evaluation on its SAME restricted inverse frame.
No chart compatibility is an input. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restrictedChart_app
    (M : X.Modules) {U W : X.Opens} (f : W ⟶ U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (A : Over W) (a : M.val.obj (op A.left)) :
    ((SchemeModuleInternalHom.overUnitChartRestrict M f e).hom.val.app (op A) a :
        Γ(X, A.left)) =
      e.hom.val.app (op (Over.mk (A.hom ≫ f))) a := rfl

private theorem restrictedChart_inv_app
    (M : X.Modules) {U W : X.Opens} (f : W ⟶ U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (A : Over W) (r : Γ(X, A.left)) :
    (SchemeModuleInternalHom.overUnitChartRestrict M f e).inv.val.app (op A) r =
      e.inv.val.app (op (Over.mk (A.hom ≫ f))) r := rfl

private theorem dualChart_restrict
    (M : X.Modules) {U W : X.Opens} (f : W ⟶ U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    SchemeModuleInternalHom.overUnitChartRestrict (SchemeModuleInternalHom.dual M) f
        (SchemeModuleInternalHom.dualOverUnitIso U e) =
      SchemeModuleInternalHom.dualOverUnitIso W
        (SchemeModuleInternalHom.overUnitChartRestrict M f e) := by
  let D := SchemeModuleInternalHom.dual M
  let eW := SchemeModuleInternalHom.overUnitChartRestrict M f e
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let A := V.unop
  let B := Over.mk (A.hom ≫ f)
  have hU : ((SchemeModuleInternalHom.dualOverUnitIso U e).hom.val.app (op B) a :
      Γ(X, A.left)) =
      SchemeModuleInternalHom.evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf)
        A.left (e.inv.val.app (op B) (1 : Γ(X, A.left))) a := by
    rw [SchemeModuleInternalHom.dualOverUnitIso_hom_val]
    rfl
  have hW : ((SchemeModuleInternalHom.dualOverUnitIso W eW).hom.val.app (op A) a :
      Γ(X, A.left)) =
      SchemeModuleInternalHom.evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf)
        A.left (eW.inv.val.app (op A) (1 : Γ(X, A.left))) a := by
    rw [SchemeModuleInternalHom.dualOverUnitIso_hom_val]
    rfl
  exact (restrictedChart_app D f (SchemeModuleInternalHom.dualOverUnitIso U e) A a).trans
    (hU.trans ((congrArg (fun m => SchemeModuleInternalHom.evaluationBilinear M
      (SheafOfModules.unit X.ringCatSheaf) A.left m a)
        (restrictedChart_inv_app M f e A (1 : Γ(X, A.left))).symm).trans hW.symm))

/-- Restricting the SAME original ideal inclusion chart gives precisely
its canonical chart on the smaller open. No frame comparison is supplied;
the installed overFunctorMap naturality proves it, including empty opens. -/
theorem schemeModuleClosedPointIdealOverCanonicalIso_restrict
    (P : closedPoints X) {U W : X.Opens} (f : W ⟶ U) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    SchemeModuleInternalHom.overUnitChartRestrict (closedImmersionModule i) f
        (schemeModuleClosedPointIdealOverCanonicalIso P U hPU) =
      schemeModuleClosedPointIdealOverCanonicalIso P W (fun h => hPU (f.le h)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let j := closedImmersionModuleToUnit i
  let theta := SheafOfModules.overFunctorMap X.ringCatSheaf f
  apply Iso.ext
  change ((theta.app M).inv ≫ (SheafOfModules.overMap X.ringCatSheaf f).map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map j)) ≫ (theta.app O).hom =
    (SheafOfModules.overFunctor X.ringCatSheaf W).map j
  have hn := theta.hom.naturality j
  change (SheafOfModules.overMap X.ringCatSheaf f).map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map j) ≫ (theta.app O).hom =
    (theta.app M).hom ≫ (SheafOfModules.overFunctor X.ringCatSheaf W).map j at hn
  rw [Category.assoc, hn, ← Category.assoc, (theta.app M).inv_hom_id, Category.id_comp]

/-- Restricting the SAME actual dual-evaluation chart gives precisely its
canonical smaller-open chart. This derives the factor-frame comparison
required to use the accepted point-stalk image in a common-complement word. -/
theorem schemeModuleClosedPointDualOverCanonicalIso_restrict
    (P : closedPoints X) {U W : X.Opens} (f : W ⟶ U) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    SchemeModuleInternalHom.overUnitChartRestrict
        (SchemeModuleInternalHom.dual (closedImmersionModule i)) f
        (schemeModuleClosedPointDualOverCanonicalIso P U hPU) =
      schemeModuleClosedPointDualOverCanonicalIso P W (fun h => hPU (f.le h)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let e := schemeModuleClosedPointIdealOverCanonicalIso P U hPU
  exact (dualChart_restrict (closedImmersionModule i) f e).trans
    (congrArg (SchemeModuleInternalHom.dualOverUnitIso W)
      (schemeModuleClosedPointIdealOverCanonicalIso_restrict P f hPU))

end PfaffianDescent
