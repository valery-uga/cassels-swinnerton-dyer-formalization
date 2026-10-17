import PfaffianDescent.VoisinP3TopCechExtComparison

/-! # Actual raw representatives of abstract ambient top cocycles -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The literal raw sections of an abstract top-degree coefficient cocycle. -/
def p3RawTopCocycleOfAbstract (m : ℕ)
    (a : DegreeThreeCocycle ((p3SectionRepresenterCechChain K).d 4 3)
      (Y := sheafOfModules PS m)) : P3RawTopCocycle K m := by
  refine ⟨p3SectionRepresenterCechHomEquiv K m 3 a.1, ?_⟩
  change (p3NegativeTwistCechComplex (K := K) m).d 3 4
    (p3SectionRepresenterCechHomEquiv K m 3 a.1) = 0
  have ha : (p3SectionRepresenterCechChain K).d 4 3 ≫ a.1 = 0 := a.2
  rw [← p3SectionRepresenterCechHomEquiv_d, ha, p3SectionRepresenterCechHomEquiv_zero]

/-- Transport to raw coefficients and back retains the actual cocycle. -/
theorem p3SectionRepresenterTopCocycleOfRaw_ofAbstract (m : ℕ)
    (a : DegreeThreeCocycle ((p3SectionRepresenterCechChain K).d 4 3)
      (Y := sheafOfModules PS m)) :
    p3SectionRepresenterTopCocycleOfRaw K m (p3RawTopCocycleOfAbstract K m a) = a := by
  apply Subtype.ext
  exact (p3SectionRepresenterCechHomEquiv K m 3).symm_apply_apply a.1

/-- The actual augmented Ext class of an abstract ambient top cocycle. -/
def p3AbstractTopCocycleToAugmentedExt [HasExt.{u} (Proj PS).Modules] (m : ℕ)
    (a : DegreeThreeCocycle ((p3SectionRepresenterCechChain K).d 4 3)
      (Y := sheafOfModules PS m)) :
    Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS m) 3 := by
  letI : CategoryTheory.Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  exact augmentedChainDegreeThreeToExt
    (p3SectionRepresenterCechTarget K)
    ((p3SectionRepresenterCechChain K).X 0)
    ((p3SectionRepresenterCechChain K).X 1)
    ((p3SectionRepresenterCechChain K).X 2)
    ((p3SectionRepresenterCechChain K).X 3)
    ((p3SectionRepresenterCechChain K).X 4)
    (sheafOfModules PS m) (p3SectionRepresenterCechAugmentation K)
    ((p3SectionRepresenterCechChain K).d 1 0)
    ((p3SectionRepresenterCechChain K).d 2 1)
    ((p3SectionRepresenterCechChain K).d 3 2)
    ((p3SectionRepresenterCechChain K).d 4 3)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf (fun i : ULift.{u} (Fin 4) => p3StandardOpen K i.down)
      ⊤ CategoryTheory.Limits.isTerminalTop)
    ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)
    ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)
    ((p3SectionRepresenterCechChain K).d_comp_d 4 3 2)
    (p3SectionRepresenterCech_augmentation_exact K)
    (p3SectionRepresenterCech_exact_one K)
    (p3SectionRepresenterCech_exact_two K)
    (p3SectionRepresenterCech_exact_three K) a

set_option backward.isDefEq.respectTransparency false in
/-- Raw transport preserves the actual top-degree Ext class. -/
theorem p3RawTopCocycleToAugmentedExt_ofAbstract
    [hExt : HasExt.{u} (Proj PS).Modules] (m : ℕ)
    (a : DegreeThreeCocycle ((p3SectionRepresenterCechChain K).d 4 3)
      (Y := sheafOfModules PS m)) :
    p3RawTopCocycleToAugmentedExt K m (p3RawTopCocycleOfAbstract K m a) =
      p3AbstractTopCocycleToAugmentedExt K m a := by
  exact congrArg (p3AbstractTopCocycleToAugmentedExt K m)
    (p3SectionRepresenterTopCocycleOfRaw_ofAbstract K m a)
end PfaffianDescent.ProjectiveNegativeTwist
