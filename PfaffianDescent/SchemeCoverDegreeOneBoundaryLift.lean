import PfaffianDescent.CechExtDegreeOneBoundaryLift
import PfaffianDescent.ExtOneCoproductVanishing

/-! Actual degree-one covering lifts and actual connecting classes.
SOURCE ONLY / UNVERIFIED. No desired comparison-map equality premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
variable {X : Scheme.{u}} {ι : Type u}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coverDegreeOneAugmentationPrecomp
    {A : Type*} [Category A] [Abelian A] [HasExt.{u} A]
    {P O Q M : A} (e : P ≅ O) (q : O ⟶ Q) (t : Ext.{u} Q M 1) :
    (Ext.mk₀ e.inv).comp ((Ext.mk₀ (e.hom ≫ q)).comp t (zero_add 1)) (zero_add 1) =
      (Ext.mk₀ q).comp t (zero_add 1) := by
  rw [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_assoc]

private theorem coverDegreeOneRawBoundary
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    [hExt : HasExt.{u} X.Modules] (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₃)
    (p : (sectionRepresenterCechChain X.ringCatSheaf U).X 0 ⟶ S.X₂)
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := S.X₁))
    (hp : p ≫ S.g = sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
      (schemeCoverCechTargetIsoUnit U).hom ≫ q)
    (hz : (sectionRepresenterCechChain X.ringCatSheaf U).d 1 0 ≫ p = z.1 ≫ S.f) :
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
    schemeCoverDegreeOneToExtHom U hU S.X₁ z =
      (Ext.mk₀ (C := X.Modules) ((schemeCoverCechTargetIsoUnit U).hom ≫ q)).comp
        hS.extClass (zero_add 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let C : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf U
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop
  let hex := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf U hU ⊤ isTerminalTop
  letI : Epi eps := hex.2
  exact augmentedChainDegreeOneToExt_eq_boundary_of_lift (A := X.Modules) eps (C.d 1 0) (C.d 2 1)
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf U ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) hex.1 (schemeCoverCech_exact_one U hU)
    S hS ((schemeCoverCechTargetIsoUnit U).hom ≫ q) p z hp hz

/-- A literal original lift in the actual covering complex represents the
original coefficient connecting class after the actual augmentation/unit Iso. -/
theorem schemeCoverDegreeOneToCohomology_eq_boundary_of_lift
    (U : ι → X.Opens) (hU : (Opens.grothendieckTopology X).CoversTop U)
    [hExt : HasExt.{u} X.Modules] (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₃)
    (p : (sectionRepresenterCechChain X.ringCatSheaf U).X 0 ⟶ S.X₂)
    (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      (Y := S.X₁))
    (hp : p ≫ S.g = sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
      (schemeCoverCechTargetIsoUnit U).hom ≫ q)
    (hz : (sectionRepresenterCechChain X.ringCatSheaf U).d 1 0 ≫ p = z.1 ≫ S.f) :
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
    (Ext.mk₀ (C := X.Modules) (schemeCoverCechTargetIsoUnit U).inv).comp
      (schemeCoverDegreeOneToExtHom U hU S.X₁ z) (zero_add 1) =
      (Ext.mk₀ (C := X.Modules) q).comp hS.extClass (zero_add 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  have h := coverDegreeOneRawBoundary U hU S hS q p z hp hz
  have hh := congrArg (fun t : Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechAugmented X.ringCatSheaf U ⊤
        isTerminalTop).right) S.X₁ 1 =>
      (Ext.mk₀ (C := X.Modules) (schemeCoverCechTargetIsoUnit U).inv).comp t (zero_add 1)) h
  exact hh.trans (coverDegreeOneAugmentationPrecomp (A := X.Modules)
    (schemeCoverCechTargetIsoUnit U) q hS.extClass)

/-- Degree-zero Ext1 acyclicity of the actual cover term constructs a
literal lift and a genuine kernel cocycle of every original global Q section. -/
theorem schemeCoverDegreeOne_exists_boundary_lift
    (U : ι → X.Opens) [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf U).X 0) S.X₁ 1)]
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₃) :
    ∃ (p : (sectionRepresenterCechChain X.ringCatSheaf U).X 0 ⟶ S.X₂)
      (z : DegreeOneCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
        (Y := S.X₁)),
      p ≫ S.g = sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
        (schemeCoverCechTargetIsoUnit U).hom ≫ q ∧
      (sectionRepresenterCechChain X.ringCatSheaf U).d 1 0 ≫ p = z.1 ≫ S.f := by
  let C : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf U
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop
  obtain ⟨p, hp⟩ := hom_postcomp_surjective_of_ext_one_subsingleton
    (show X.Modules from C.X 0) S hS (eps ≫ (schemeCoverCechTargetIsoUnit U).hom ≫ q)
  have hpNative : (p : C.X 0 ⟶ S.X₂) ≫ S.g =
      eps ≫ (schemeCoverCechTargetIsoUnit U).hom ≫ q := hp
  have hzero : (C.d 1 0 ≫ p) ≫ S.g = 0 := by
    rw [Category.assoc, hpNative, ← Category.assoc,
      sectionRepresenterCech_d_one_zero_comp_augmentation, zero_comp]
  let a : C.X 1 ⟶ S.X₁ := hS.fIsKernel.lift (KernelFork.ofι (C.d 1 0 ≫ p) hzero)
  have ha : a ≫ S.f = C.d 1 0 ≫ p :=
    hS.fIsKernel.fac (KernelFork.ofι (C.d 1 0 ≫ p) hzero) WalkingParallelPair.zero
  letI : Mono S.f := hS.mono_f
  have haz : C.d 2 1 ≫ a = 0 := by
    apply (cancel_mono S.f).1
    rw [Category.assoc, ha, ← Category.assoc, C.d_comp_d 2 1 0, zero_comp, zero_comp]
  exact ⟨p, ⟨a, haz⟩, hp, ha.symm⟩

end PfaffianDescent
end
