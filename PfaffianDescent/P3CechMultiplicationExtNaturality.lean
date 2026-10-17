import PfaffianDescent.P3QuadraticCanonicalTrace
import PfaffianDescent.DegreeThreeResolutionNaturality
import PfaffianDescent.SectionRepresenterCechCoefficientNaturality

/-! # Actual multiplication through the ambient Cech-to-Ext comparison -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial Opposite
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
theorem p3SectionRepresenterCechHomEquiv_mulHomogeneous
    (m d n : ℕ) (q : PS d)
    (h : (p3SectionRepresenterCechChain K).X n ⟶ sheafOfModules PS (m + d)) :
    p3SectionRepresenterCechHomEquiv K m n (h ≫ mulHomogeneous PS q m) =
      (p3NegativeTwistCechMultiplication K m d q).f n
        (p3SectionRepresenterCechHomEquiv K (m + d) n h) := by
  apply (p3NegativeTwistCechTermEquivPi K m n).injective
  funext f
  rw [p3SectionRepresenterCechHomEquiv_apply,
    sectionRepresenterCechHomEquivPi_postcomp,
    p3NegativeTwistCechTermEquivPi_apply]
  have ht := congrArg (fun t => t (p3SectionRepresenterCechHomEquiv K (m + d) n h))
    (p3NegativeTwistCechMultiplication_projection K m d n q f)
  simp only [ConcreteCategory.comp_apply] at ht
  calc
    _ = (mulHomogeneousPresheaf PS q m).app
        (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a)))
        (p3NegativeTwistCechTermEquivPi K (m + d) n
          (p3SectionRepresenterCechHomEquiv K (m + d) n h) f) :=
      congrArg (fun s => (mulHomogeneousPresheaf PS q m).app
        (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a))) s)
        (p3SectionRepresenterCechHomEquiv_apply K (m + d) n h f).symm
    _ = (mulHomogeneousPresheaf PS q m).app
        (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a)))
        ((Pi.π (p3CechTermFamily K (m + d) n) f)
          (p3SectionRepresenterCechHomEquiv K (m + d) n h)) :=
      congrArg (fun s => (mulHomogeneousPresheaf PS q m).app
        (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a))) s)
        (p3NegativeTwistCechTermEquivPi_apply K (m + d) n _ f)
    _ = _ := ht.symm

set_option backward.isDefEq.respectTransparency false in
theorem p3SectionRepresenterTopCocycleOfRaw_mulHomogeneous
    (m d : ℕ) (q : PS d) (w : P3RawTopCocycle K (m + d)) :
    p3SectionRepresenterTopCocycleOfRaw K m (p3RawTopCocycleMultiply K m d q w) =
      DegreeThreeCocycle.postcompAddHom ((p3SectionRepresenterCechChain K).d 4 3)
        (mulHomogeneous PS q m) (p3SectionRepresenterTopCocycleOfRaw K (m + d) w) := by
  apply Subtype.ext
  apply (p3SectionRepresenterCechHomEquiv K m 3).injective
  change p3SectionRepresenterCechHomEquiv K m 3
      ((p3SectionRepresenterCechHomEquiv K m 3).symm _) =
    p3SectionRepresenterCechHomEquiv K m 3
      ((p3SectionRepresenterCechHomEquiv K (m + d) 3).symm w.1 ≫ mulHomogeneous PS q m)
  rw [Equiv.apply_symm_apply, p3SectionRepresenterCechHomEquiv_mulHomogeneous,
    Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem p3RawTopCocycleToAugmentedExt_mulHomogeneous
    [hExt : HasExt.{u} (Proj PS).Modules]
    (m d : ℕ) (q : PS d) (w : P3RawTopCocycle K (m + d)) :
    (p3RawTopCocycleToAugmentedExt K (m + d) w).comp
        (Ext.mk₀ (mulHomogeneous PS q m)) (add_zero 3) =
      p3RawTopCocycleToAugmentedExt K m (p3RawTopCocycleMultiply K m d q w) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  unfold p3RawTopCocycleToAugmentedExt
  rw [augmentedChainDegreeThreeToExt_postcomp,
    p3SectionRepresenterTopCocycleOfRaw_mulHomogeneous]

end PfaffianDescent.ProjectiveNegativeTwist
