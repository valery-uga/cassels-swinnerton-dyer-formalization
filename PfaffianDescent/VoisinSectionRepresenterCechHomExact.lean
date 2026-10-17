import PfaffianDescent.VoisinSectionRepresenterCechDifferential
import PfaffianDescent.VoisinTwistCechExact

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
universe u
namespace PfaffianDescent.ProjectiveNegativeTwist

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
lemma p3SectionRepresenterCechHomEquiv_zero (m n : ℕ) :
    p3SectionRepresenterCechHomEquiv K m n
      (0 : (p3SectionRepresenterCechChain K).X n ⟶ sheafOfModules PS m) = 0 := by
  apply (p3NegativeTwistCechTermEquivPi K m n).injective
  funext f
  rw [p3SectionRepresenterCechHomEquiv_apply,
    p3NegativeTwistCechTermEquivPi_apply]
  change (sectionRepresenterCechHomAddEquivPi (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) => p3StandardOpen (K := K) i.down)
      (sheafOfModules PS m) n) 0 (fun j => ULift.up (f j)) = _
  rw [map_zero]
  change 0 = ((Pi.π (p3CechTermFamily K m n) f).hom) 0
  rw [map_zero]

set_option backward.isDefEq.respectTransparency false in
lemma p3SectionRepresenterCechHomEquiv_add (m n : ℕ)
    (x y : (p3SectionRepresenterCechChain K).X n ⟶
      sheafOfModules PS m) :
    p3SectionRepresenterCechHomEquiv K m n (x + y) =
      p3SectionRepresenterCechHomEquiv K m n x +
        p3SectionRepresenterCechHomEquiv K m n y := by
  apply (p3NegativeTwistCechTermEquivPi K m n).injective
  funext f
  calc
    p3NegativeTwistCechTermEquivPi K m n
        (p3SectionRepresenterCechHomEquiv K m n (x + y)) f =
        sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
          (fun i : ULift.{u} (Fin 4) =>
            p3StandardOpen (K := K) i.down)
          (sheafOfModules PS m) n (x + y)
          (fun j => ULift.up (f j)) :=
      p3SectionRepresenterCechHomEquiv_apply K m n (x + y) f
    _ = sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
          (fun i : ULift.{u} (Fin 4) =>
            p3StandardOpen (K := K) i.down)
          (sheafOfModules PS m) n x (fun j => ULift.up (f j)) +
        sectionRepresenterCechHomEquivPi (Proj PS).ringCatSheaf
          (fun i : ULift.{u} (Fin 4) =>
            p3StandardOpen (K := K) i.down)
          (sheafOfModules PS m) n y (fun j => ULift.up (f j)) := by
      exact congrFun (map_add
        (sectionRepresenterCechHomAddEquivPi (Proj PS).ringCatSheaf
          (fun i : ULift.{u} (Fin 4) =>
            p3StandardOpen (K := K) i.down)
          (sheafOfModules PS m) n) x y) (fun j => ULift.up (f j))
    _ = p3NegativeTwistCechTermEquivPi K m n
          (p3SectionRepresenterCechHomEquiv K m n x) f +
        p3NegativeTwistCechTermEquivPi K m n
          (p3SectionRepresenterCechHomEquiv K m n y) f := by
      rw [p3SectionRepresenterCechHomEquiv_apply,
        p3SectionRepresenterCechHomEquiv_apply]
    _ = p3NegativeTwistCechTermEquivPi K m n
          (p3SectionRepresenterCechHomEquiv K m n x +
            p3SectionRepresenterCechHomEquiv K m n y) f := by
      exact congrFun (p3NegativeTwistCechTermEquivPi_add K m n
        (p3SectionRepresenterCechHomEquiv K m n x)
        (p3SectionRepresenterCechHomEquiv K m n y)).symm f

/-- Applying `Hom(-, O(-m))` to the section-representer Cech chain is exact
in cochain degree one. -/
lemma p3SectionRepresenterCechHom_exact_one (m : ℕ) :
    Function.Exact
      (fun h : (p3SectionRepresenterCechChain K).X 0 ⟶ sheafOfModules PS m =>
        (p3SectionRepresenterCechChain K).d 1 0 ≫ h)
      (fun h : (p3SectionRepresenterCechChain K).X 1 ⟶ sheafOfModules PS m =>
        (p3SectionRepresenterCechChain K).d 2 1 ≫ h) := by
  intro y
  constructor
  · intro hy
    change (p3SectionRepresenterCechChain K).d 2 1 ≫ y = 0 at hy
    have hy' :
        (p3NegativeTwistCechComplex (K := K) m).d 1 2
          (p3SectionRepresenterCechHomEquiv K m 1 y) = 0 := by
      calc
        _ = p3SectionRepresenterCechHomEquiv K m 2
            ((p3SectionRepresenterCechChain K).d 2 1 ≫ y) :=
          (p3SectionRepresenterCechHomEquiv_d K m 1 y).symm
        _ = p3SectionRepresenterCechHomEquiv K m 2 0 :=
          congrArg (p3SectionRepresenterCechHomEquiv K m 2) hy
        _ = 0 := p3SectionRepresenterCechHomEquiv_zero K m 2
    obtain ⟨x, hx⟩ :=
      (p3NegativeTwistCech_exact_one K m
        (p3SectionRepresenterCechHomEquiv K m 1 y)).mp hy'
    let x' := (p3SectionRepresenterCechHomEquiv K m 0).symm x
    refine ⟨x', ?_⟩
    apply (p3SectionRepresenterCechHomEquiv K m 1).injective
    rw [p3SectionRepresenterCechHomEquiv_d]
    simpa only [x', Equiv.apply_symm_apply] using hx
  · rintro ⟨x, rfl⟩
    change (p3SectionRepresenterCechChain K).d 2 1 ≫
      ((p3SectionRepresenterCechChain K).d 1 0 ≫ x) = 0
    rw [← Category.assoc,
      (p3SectionRepresenterCechChain K).d_comp_d 2 1 0, zero_comp]

/-- Applying `Hom(-, O(-m))` to the section-representer Cech chain is exact
in cochain degree two. -/
lemma p3SectionRepresenterCechHom_exact_two (m : ℕ) :
    Function.Exact
      (fun h : (p3SectionRepresenterCechChain K).X 1 ⟶ sheafOfModules PS m =>
        (p3SectionRepresenterCechChain K).d 2 1 ≫ h)
      (fun h : (p3SectionRepresenterCechChain K).X 2 ⟶ sheafOfModules PS m =>
        (p3SectionRepresenterCechChain K).d 3 2 ≫ h) := by
  intro z
  constructor
  · intro hz
    change (p3SectionRepresenterCechChain K).d 3 2 ≫ z = 0 at hz
    have hz' :
        (p3NegativeTwistCechComplex (K := K) m).d 2 3
          (p3SectionRepresenterCechHomEquiv K m 2 z) = 0 := by
      calc
        _ = p3SectionRepresenterCechHomEquiv K m 3
            ((p3SectionRepresenterCechChain K).d 3 2 ≫ z) :=
          (p3SectionRepresenterCechHomEquiv_d K m 2 z).symm
        _ = p3SectionRepresenterCechHomEquiv K m 3 0 :=
          congrArg (p3SectionRepresenterCechHomEquiv K m 3) hz
        _ = 0 := p3SectionRepresenterCechHomEquiv_zero K m 3
    obtain ⟨y, hy⟩ :=
      (p3NegativeTwistCech_exact_two K m
        (p3SectionRepresenterCechHomEquiv K m 2 z)).mp hz'
    let y' := (p3SectionRepresenterCechHomEquiv K m 1).symm y
    refine ⟨y', ?_⟩
    apply (p3SectionRepresenterCechHomEquiv K m 2).injective
    rw [p3SectionRepresenterCechHomEquiv_d]
    simpa only [y', Equiv.apply_symm_apply] using hy
  · rintro ⟨y, rfl⟩
    change (p3SectionRepresenterCechChain K).d 3 2 ≫
      ((p3SectionRepresenterCechChain K).d 2 1 ≫ y) = 0
    rw [← Category.assoc,
      (p3SectionRepresenterCechChain K).d_comp_d 3 2 1, zero_comp]

end PfaffianDescent.ProjectiveNegativeTwist
