import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! Native cokernel-to-cokernel map and exact connecting naturality for
actual unit sequences. This is a generic map construction, not existence
of the geometric point-to-original-line map or nonzero residue trace.
SOURCE ONLY / UNVERIFIED; root owns all compiler checks. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe u
variable {X : Scheme.{u}} {A B : X.Modules}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The quotient map is the native factor of the original target projection.
Both categorical cokernels remain literal. The generic input is an ordinary
morphism and its original commutative square, not a boundary certificate. -/
def actualUnitCokernelMap184
    (delta : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ A)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ B)
    (t : A ⟶ B) (ht : delta ≫ t = phi) : cokernel (C := X.Modules) delta ⟶ cokernel (C := X.Modules) phi :=
  cokernel.desc (C := X.Modules) delta (t ≫ cokernel.π (C := X.Modules) phi) (by
    rw [← Category.assoc, ht, cokernel.condition (C := X.Modules)])

/-- The original categorical projections satisfy the native square. -/
theorem actualUnitCokernelMap_projection184
    (delta : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ A)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ B)
    (t : A ⟶ B) (ht : delta ≫ t = phi) :
    cokernel.π (C := X.Modules) delta ≫ actualUnitCokernelMap184 delta phi t ht = t ≫ cokernel.π (C := X.Modules) phi :=
  cokernel.π_desc (C := X.Modules) _ _ _

/-- Actual short-complex map with identity on the SAME unit coefficient. -/
def actualUnitCokernelSequenceMap184
    (delta : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ A)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ B)
    (t : A ⟶ B) (ht : delta ≫ t = phi) :
    ShortComplex.cokernelSequence (C := X.Modules) delta ⟶ ShortComplex.cokernelSequence (C := X.Modules) phi :=
  ShortComplex.homMk (C := X.Modules) (𝟙 _) t (actualUnitCokernelMap184 delta phi t ht)
    ((Category.id_comp phi).trans ht.symm)
    (actualUnitCokernelMap_projection184 delta phi t ht).symm

/-- The SAME original native extension classes satisfy exact naturality.
Geometric callers still have to construct t and its actual square. -/
theorem actualUnitCokernel_extClass_naturality184 [hExt : HasExt.{u} X.Modules]
    (delta : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ A)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ B)
    (t : A ⟶ B) (ht : delta ≫ t = phi)
    (hdelta : (ShortComplex.cokernelSequence (C := X.Modules) delta).ShortExact)
    (hphi : (ShortComplex.cokernelSequence (C := X.Modules) phi).ShortExact) :
    ((ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hdelta) : Ext.{u} (C := X.Modules)
      (cokernel (C := X.Modules) delta)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1) = (Ext.mk₀.{u} (C := X.Modules) (actualUnitCokernelMap184 delta phi t ht)).comp
      (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi) (zero_add 1) := by
  have h := ShortComplex.ShortExact.extClass_naturality.{u} (C := X.Modules) hdelta hphi
    (actualUnitCokernelSequenceMap184 delta phi t ht)
  change (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hdelta).comp (Ext.mk₀.{u} (C := X.Modules) (𝟙 _)) (add_zero 1) = _ at h
  rw [Ext.comp_mk₀_id (C := X.Modules)] at h
  exact h

/-- Actual unit-Hom connecting equality follows by Yoneda associativity. -/
theorem actualUnitCokernel_unitHomConnecting_eq184 [hExt : HasExt.{u} X.Modules]
    (delta : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ A)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ B)
    (t : A ⟶ B) (ht : delta ≫ t = phi)
    (hdelta : (ShortComplex.cokernelSequence (C := X.Modules) delta).ShortExact)
    (hphi : (ShortComplex.cokernelSequence (C := X.Modules) phi).ShortExact)
    (c : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ cokernel (C := X.Modules) delta) :
    (Ext.mk₀.{u} (C := X.Modules) c).comp (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hdelta) (zero_add 1) =
      (Ext.mk₀.{u} (C := X.Modules) (c ≫ actualUnitCokernelMap184 delta phi t ht)).comp (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi) (zero_add 1) := by
  rw [actualUnitCokernel_extClass_naturality184 delta phi t ht hdelta hphi]
  exact Ext.mk₀_comp_mk₀_assoc.{u} (C := X.Modules) c
    (actualUnitCokernelMap184 delta phi t ht)
    (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi)

/-- The point quotient's actual global sections map into the literal whole
quotient, and both connecting maps use the SAME original pi scalar action. -/
theorem actualUnitCokernel_openTopConnecting_eq184
    {K : Type u} [Field K] [hExt : HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (delta : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ A)
    (phi : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ B)
    (t : A ⟶ B) (ht : delta ≫ t = phi)
    (hdelta : (ShortComplex.cokernelSequence (C := X.Modules) delta).ShortExact)
    (hphi : (ShortComplex.cokernelSequence (C := X.Modules) phi).ShortExact)
    (c : SchemeModuleOpenSectionsOver pi (cokernel (C := X.Modules) delta) ⊤) :
    Coray.schemeModuleOpenTopConnectingLinearMapOver pi
        (ShortComplex.cokernelSequence (C := X.Modules) delta) hdelta c =
      Coray.schemeModuleOpenTopConnectingLinearMapOver pi
        (ShortComplex.cokernelSequence (C := X.Modules) phi) hphi
        (Coray.schemeModuleOpenTopCoefficientLinearMapOver pi
          (actualUnitCokernelMap184 delta phi t ht) c) := by
  letI : Linear K X.Modules := Coray.schemeModulesLinearOver pi
  let eD := Coray.schemeModuleUnitHomGroundLinearEquivOpenTop pi (cokernel (C := X.Modules) delta)
  let eQ := Coray.schemeModuleUnitHomGroundLinearEquivOpenTop pi (cokernel (C := X.Modules) phi)
  let q := actualUnitCokernelMap184 delta phi t ht
  have hc : eD.symm c ≫ q = eQ.symm (q.val.app (op ⊤) c) := by
    apply eQ.injective
    rw [Coray.schemeModuleUnitHomGroundLinearEquivOpenTop_naturality,
      eD.apply_symm_apply, eQ.apply_symm_apply]
  change (Ext.mk₀.{u} (C := X.Modules) (eD.symm c)).comp (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hdelta) (zero_add 1) =
    (Ext.mk₀.{u} (C := X.Modules) (eQ.symm (q.val.app (op ⊤) c))).comp (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi) (zero_add 1)
  exact (actualUnitCokernel_unitHomConnecting_eq184 delta phi t ht hdelta hphi (eD.symm c)).trans
    (congrArg (fun f => (Ext.mk₀.{u} (C := X.Modules) f).comp (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hphi) (zero_add 1)) hc)

end PfaffianDescent
