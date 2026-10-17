import PfaffianDescent.ThreeQuadricNegativeChartCoefficients
import PfaffianDescent.IntrinsicFullQuadraticSystem
import PfaffianDescent.IdealSheafModule

/-! SOURCE ONLY / UNVERIFIED. A homogeneous quadric which vanishes in the
actual four affine immersion kernels induces the actual negative-twist map
into the SAME immersion ideal. The geometric triple caller derives this
primitive ideal membership, rather than assuming an image comparison. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
-- Actual production exposes Proj/sheaf/site aliases at naturality and ring maps.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Specialize the canonical kernel and original ideal before any rich Proj
or graded module dictionaries are substituted. -/
private def negativeQuadricClosedImmersionIdealLift
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : X.Modules) (m : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hm : m ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i = 0) :
    M ⟶ IdealSheafDataModule.closedImmersionModule i := by
  let k : M ⟶ IdealSheafDataModule.closedImmersionKernelModule i :=
    kernel.lift (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) m hm
  exact k ≫ (IdealSheafDataModule.closedImmersionModuleToKernelIso i).inv

private theorem negativeQuadricClosedImmersionIdealLift_comp
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : X.Modules) (m : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hm : m ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i = 0) :
    negativeQuadricClosedImmersionIdealLift i M m hm ≫
      IdealSheafDataModule.closedImmersionModuleToUnit i = m := by
  let e := IdealSheafDataModule.closedImmersionModuleToKernelIso i
  have hi : e.inv ≫ IdealSheafDataModule.closedImmersionModuleToUnit i =
      IdealSheafDataModule.closedImmersionKernelModuleToUnit i := by
    calc
      _ = e.inv ≫ (e.hom ≫ IdealSheafDataModule.closedImmersionKernelModuleToUnit i) :=
        congrArg (fun z => e.inv ≫ z)
          (IdealSheafDataModule.closedImmersionModuleToKernel_comp i).symm
      _ = _ := e.inv_hom_id_assoc _
  unfold negativeQuadricClosedImmersionIdealLift
  rw [Category.assoc, hi]
  exact kernel.lift_ι _ _ _

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Vanishing is tested on the actual scheme maps, including nilpotents. -/
theorem p3NegativeQuadric_comp_augmentation_zero
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (q : PS 2) (hq : ∀ j : Fin 4, q.val ∈ intrinsicQuadraticChartIdeal i j) :
    mulHomogeneousToUnit PS q ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i = 0 := by
  let M := sheafOfModules PS 2
  let Q := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let φ := mulHomogeneousToUnit PS q ≫
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  ext U z
  apply TopCat.Presheaf.IsSheaf.section_ext Q.isSheaf
  intro x hx
  have hxcover : x ∈ ⨆ j : Fin 4, p3StandardOpen (K := K) j := by
    rw [p3StandardOpen_iSup K]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxcover
  let V := U.unop ⊓ p3StandardOpen (K := K) j
  let hVU : V ≤ U.unop := inf_le_left
  let hVj : V ≤ p3StandardOpen (K := K) j := inf_le_right
  let zV := M.presheaf.map (homOfLE hVU).op z
  let rj : Γ(Proj PS, p3StandardOpen (K := K) j) :=
    (Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j q.val)
  have hrj : i.app (p3StandardOpen (K := K) j) rj = 0 := by
    have h := hq j
    change rj ∈ i.ker.ideal (intrinsicQuadraticAmbientOpen j) at h
    rw [i.ker_apply (intrinsicQuadraticAmbientOpen j)] at h
    exact h
  have hnat := ConcreteCategory.congr_hom (i.naturality (homOfLE hVj).op) rj
  change i.app V ((Proj PS).presheaf.map (homOfLE hVj).op rj) =
    Z.presheaf.map ((Opens.map i.base).map (homOfLE hVj)).op
      (i.app (p3StandardOpen (K := K) j) rj) at hnat
  have hr : i.app V (p3NegativeQuadricChartCoefficient K j V hVj q) = 0 := by
    change i.app V ((Proj PS).presheaf.map (homOfLE hVj).op rj) = 0
    exact hnat.trans ((congrArg
      (fun t => Z.presheaf.map ((Opens.map i.base).map (homOfLE hVj)).op t) hrj).trans
        (Z.presheaf.map ((Opens.map i.base).map (homOfLE hVj)).op).hom.map_zero)
  have hz : φ.val.app (op V) zV = 0 := by
    change (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i).val.app (op V)
      ((mulHomogeneousToUnit PS q).val.app (op V) zV) = 0
    erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
    change (i.app V).hom ((mulHomogeneousToUnit PS q).val.app (op V) zV) = 0
    let a : Γ(Proj PS, V) := p3NegativeQuadricChartCoefficient K j V hVj q
    let b : Γ(Proj PS, V) := (negativeTwistTrivializationHom K j 2).val.app (op V) zV
    have hcoeff := p3NegativeQuadric_mulToUnit_chartCoefficient K j V hVj q zV
    calc
      _ = (i.app V).hom (@Mul.mul (Γ(Proj PS, V))
          (inferInstance : Mul (Γ(Proj PS, V))) a b) :=
        congrArg (fun t : Γ(Proj PS, V) => (i.app V).hom t) hcoeff
      _ = (i.app V).hom a * (i.app V).hom b := (i.app V).hom.map_mul a b
      _ = 0 := (congrArg (fun t : Γ(Z, i ⁻¹ᵁ V) => t * (i.app V).hom b) hr).trans
        (zero_mul _)
  refine ⟨V, hVU, ⟨hx, hj⟩, ?_⟩
  have hres := ConcreteCategory.congr_hom (φ.val.naturality (homOfLE hVU).op) z
  change Q.presheaf.map (homOfLE hVU).op (φ.val.app U z) =
    Q.presheaf.map (homOfLE hVU).op 0
  rw [map_zero]
  exact hres.symm.trans hz

/-- Actual factorization through the original closed-immersion ideal,
using its checked identification with the kernel module. -/
def p3NegativeQuadricToOriginalIdeal
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (q : PS 2) (hq : ∀ j : Fin 4, q.val ∈ intrinsicQuadraticChartIdeal i j) :
    sheafOfModules PS 2 ⟶ IdealSheafDataModule.closedImmersionModule i := by
  exact negativeQuadricClosedImmersionIdealLift i (sheafOfModules PS 2)
    (show sheafOfModules PS 2 ⟶ SheafOfModules.unit (Proj PS).ringCatSheaf from
      mulHomogeneousToUnit PS (d := 2) q) (p3NegativeQuadric_comp_augmentation_zero i q hq)

@[reassoc]
theorem p3NegativeQuadricToOriginalIdeal_comp
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (q : PS 2) (hq : ∀ j : Fin 4, q.val ∈ intrinsicQuadraticChartIdeal i j) :
    p3NegativeQuadricToOriginalIdeal i q hq ≫
      IdealSheafDataModule.closedImmersionModuleToUnit i = mulHomogeneousToUnit PS q := by
  exact negativeQuadricClosedImmersionIdealLift_comp i (sheafOfModules PS 2)
    (show sheafOfModules PS 2 ⟶ SheafOfModules.unit (Proj PS).ringCatSheaf from
      mulHomogeneousToUnit PS (d := 2) q) (p3NegativeQuadric_comp_augmentation_zero i q hq)

end PfaffianDescent.ProjectiveNegativeTwist
