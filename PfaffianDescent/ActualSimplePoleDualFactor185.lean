import PfaffianDescent.ActualRankOneIdealDualContraction185
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! SOURCE ONLY / UNVERIFIED. Explicit contraction of the actual factor
v : O→I tensor M gives a map dual(I)→M. Its unit square is a conclusion,
proved for the SAME inclusion and SAME v. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma schemeModuleIdealTensorInclusion_swapped185
    (I M : X.Modules) (j : I ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (schemeModuleTensorSymmetry I M).hom ≫ schemeModuleTensorMap (𝟙 M) j ≫
      (schemeModuleTensorUnitRightIso M).hom =
    schemeModuleTensorMap j (𝟙 M) ≫ (schemeModuleTensorUnitLeftIso M).hom := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let b := schemeModuleTensorSymmetry M O
  let l := schemeModuleTensorUnitLeftIso M
  let r := schemeModuleTensorUnitRightIso M
  have hu : (schemeModuleTensorSymmetry O M).hom ≫ r.hom = l.hom := by
    have hb : b.hom ≫ l.hom = r.hom := schemeModuleTensorSymmetry_unit_leftUnitor M
    have h := congrArg (fun z : schemeModuleTensor M O ⟶ M => b.inv ≫ z) hb
    have h' : l.hom = b.inv ≫ r.hom := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
    exact (congrArg (fun z : schemeModuleTensor O M ⟶ schemeModuleTensor M O =>
      z ≫ r.hom) (schemeModuleTensorSymmetry_inv_eq M O)).symm.trans h'.symm
  have hn := schemeModuleTensorSymmetry_naturality j (𝟙 M)
  calc
    _ = (schemeModuleTensorMap j (𝟙 M) ≫
        (schemeModuleTensorSymmetry O M).hom) ≫ r.hom := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun z : schemeModuleTensor I M ⟶ schemeModuleTensor M O =>
          z ≫ r.hom) hn.symm)
    _ = schemeModuleTensorMap j (𝟙 M) ≫ l.hom := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z : schemeModuleTensor O M ⟶ M =>
          schemeModuleTensorMap j (𝟙 M) ≫ z) hu)

/-- The actual map is built from v and actual evaluation; hI supplies
invertibility internally, without a duality certificate. -/
def schemeModuleSimplePoleDualFactor185
    (I M : X.Modules) (hI : schemeModuleLocallyRankOne I)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleTensor I M) :
    SchemeModuleInternalHom.dual I ⟶ M :=
  (schemeModuleTensorUnitRightIso (SchemeModuleInternalHom.dual I)).inv ≫
    schemeModuleTensorMap (𝟙 (SchemeModuleInternalHom.dual I))
      (v ≫ (schemeModuleTensorSymmetry I M).hom) ≫
    (schemeModuleTensorSymmetry (SchemeModuleInternalHom.dual I)
      (schemeModuleTensor M I)).hom ≫
    schemeModuleRankOneOriginalDualContraction185 I M hI

/-- The exact original unit square, derived from the actual factor v. -/
theorem schemeModuleSimplePoleDualFactor_unitSquare185
    (I M : X.Modules) (hI : schemeModuleLocallyRankOne I)
    (j : I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleTensor I M) :
    SchemeModuleInternalHom.unitToHom j ≫ schemeModuleSimplePoleDualFactor185 I M hI v =
      v ≫ (schemeModuleTensorMap j (𝟙 M) ≫ (schemeModuleTensorUnitLeftIso M).hom) := by
  let D := SchemeModuleInternalHom.dual I
  let A := schemeModuleTensor M I
  let delta := SchemeModuleInternalHom.unitToHom j
  let w := v ≫ (schemeModuleTensorSymmetry I M).hom
  let C := schemeModuleRankOneOriginalDualContraction185 I M hI
  let betaR := schemeModuleTensorMap (𝟙 M) j ≫ (schemeModuleTensorUnitRightIso M).hom
  let d := delta.val.app (op ⊤) (1 : Γ(X, ⊤))
  let a := w.val.app (op ⊤) (1 : Γ(X, ⊤))
  apply M.unitHomEquiv.injective
  apply (schemeModuleSectionsEquivTop M).injective
  change (delta ≫ schemeModuleSimplePoleDualFactor185 I M hI v).val.app (op ⊤) (1 : Γ(X, ⊤)) =
    (v ≫ (schemeModuleTensorMap j (𝟙 M) ≫
      (schemeModuleTensorUnitLeftIso M).hom)).val.app (op ⊤) (1 : Γ(X, ⊤))
  have hl : (delta ≫ schemeModuleSimplePoleDualFactor185 I M hI v).val.app
      (op ⊤) (1 : Γ(X, ⊤)) = C.val.app (op ⊤) (actualModuleLocalTensorSection A D ⊤ a d) := by
    change C.val.app (op ⊤)
      ((schemeModuleTensorSymmetry D A).hom.val.app (op ⊤)
        (((schemeModuleTensorUnitRightIso D).inv ≫
          schemeModuleTensorMap (𝟙 D) w).val.app (op ⊤) d)) = _
    rw [actualModuleLocalTensorRightUnitInsert185, actualModuleLocalTensorSymmetry185]
  have hi : ((schemeModuleTensorUnitRightIso A).inv ≫
      schemeModuleTensorMap (𝟙 A) delta ≫ C).val.app (op ⊤) a =
        C.val.app (op ⊤) (actualModuleLocalTensorSection A D ⊤ a d) := by
    change C.val.app (op ⊤)
      (((schemeModuleTensorUnitRightIso A).inv ≫ schemeModuleTensorMap (𝟙 A) delta).val.app
        (op ⊤) a) = _
    exact congrArg (fun z : (schemeModuleTensor A D).val.obj (op ⊤) =>
      C.val.app (op ⊤) z)
      (actualModuleLocalTensorRightUnitInsert185 A D delta ⊤ a)
  have ha : ((schemeModuleTensorUnitRightIso A).inv ≫
      schemeModuleTensorMap (𝟙 A) delta ≫ C).val.app (op ⊤) a =
        betaR.val.app (op ⊤) a :=
    congrArg (fun f : A ⟶ M => f.val.app (op ⊤) a)
      (schemeModuleRankOneOriginalDualContraction_action185 I M hI j)
  have hs : (v ≫ (schemeModuleTensorSymmetry I M).hom ≫ betaR) =
      v ≫ (schemeModuleTensorMap j (𝟙 M) ≫ (schemeModuleTensorUnitLeftIso M).hom) := by
    exact congrArg (fun f : schemeModuleTensor I M ⟶ M => v ≫ f)
      (schemeModuleIdealTensorInclusion_swapped185 I M j)
  calc
    _ = C.val.app (op ⊤) (actualModuleLocalTensorSection A D ⊤ a d) := hl
    _ = betaR.val.app (op ⊤) a := hi.symm.trans ha
    _ = (v ≫ (schemeModuleTensorMap j (𝟙 M) ≫
        (schemeModuleTensorUnitLeftIso M).hom)).val.app (op ⊤) (1 : Γ(X, ⊤)) :=
      congrArg (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ M =>
        f.val.app (op ⊤) (1 : Γ(X, ⊤))) hs

end PfaffianDescent
