import PfaffianDescent.PlaneNativeChartLaurentFaceNaturality
import PfaffianDescent.PlanePositiveNativeCechTerms

/-! Native terms of the CANONICAL negative-twist coordinate-cover Čech complex.
No comparison equivalence or cohomology statement is supplied as a premise.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open ProjectiveNegativeTwist PlaneLaurentLocalization PlaneTwistLaurent PlaneTwistCechTerms
open PlaneTwistCechTerms.GenericEvaluation
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K

/-- The actual Mathlib Čech complex of the SAME negative-twist presheaf
on the original three coordinate opens. -/
def p2NegativeNativeCechComplex (m : ℕ) : CochainComplex AddCommGrpCat ℕ :=
  (CategoryTheory.cechComplexFunctor (p2StandardOpen (K := K))).obj
    (sheafOfModules PS m).presheaf

/-- The actual canonical categorical section factor of one native term. -/
abbrev p2NegativeNativeCechTermFamily (m n : ℕ)
    (f : Fin (n + 1) → Fin 3) : AddCommGrpCat :=
  (sheafOfModules PS m).presheaf.obj
    (op (∏ᶜ fun a : Fin (n + 1) => p2StandardOpen (K := K) (f a)))

/-- Only equality of the OWN canonical opens is used to present a native
categorical term factor as native sections on its denominator basic open. -/
def p2NegativeNativeCechComponentIsoBasic (m n : ℕ)
    (f : Fin (n + 1) → Fin 3) :
    p2NegativeNativeCechTermFamily K m n f ≅
      Γ(sheafOfModules PS m, p2CechBasicOpen K n f) :=
  (sheafOfModules PS m).presheaf.mapIso
    (eqToIso ((p2CechProduct_eq_inf K n f).trans
      (p2CechBasicOpen_eq_inf (K := K) n f).symm)).op.symm

/-- Every actual canonical term is the family of its OWN native section
factors, through the existing categorical product projections. -/
def p2NegativeNativeCechTermAddEquivSections (m n : ℕ) :
    (p2NegativeNativeCechComplex K m).X n ≃+
      (∀ f : Fin (n + 1) → Fin 3,
        Γ(sheafOfModules PS m, p2CechBasicOpen K n f)) :=
  (addCommGrpProductAddEquivPi (p2NegativeNativeCechTermFamily K m n)).trans
    (AddEquiv.piCongrRight fun f =>
      addCommGrpIsoAddEquiv (p2NegativeNativeCechComponentIsoBasic K m n f))

/-- Evaluation is the actual product projection followed by the actual
native open-equality map; this fixes the comparison map explicitly. -/
theorem p2NegativeNativeCechTermAddEquivSections_apply
    (m n : ℕ) (x : (p2NegativeNativeCechComplex K m).X n)
    (f : Fin (n + 1) → Fin 3) :
    p2NegativeNativeCechTermAddEquivSections K m n x f =
      (p2NegativeNativeCechComponentIsoBasic K m n f).hom
        ((Pi.π (p2NegativeNativeCechTermFamily K m n) f) x) := by
  change (p2NegativeNativeCechComponentIsoBasic K m n f).hom
    (addCommGrpProductAddEquivPi (p2NegativeNativeCechTermFamily K m n) x f) = _
  exact congrArg
    (fun y : p2NegativeNativeCechTermFamily K m n f =>
      (p2NegativeNativeCechComponentIsoBasic K m n f).hom y)
    (addCommGrpProductAddEquivPi_apply
      (p2NegativeNativeCechTermFamily K m n)
      (show (∏ᶜ p2NegativeNativeCechTermFamily K m n : AddCommGrpCat) from x) f)

/-- The canonical negative-twist Čech term has its actual restored Laurent
representatives, formed from its OWN native sections. -/
def p2NegativeNativeCechTermToLaurent (m n : ℕ) :
    (p2NegativeNativeCechComplex K m).X n →+
      ((Fin (n + 1) → Fin 3) → PlaneLaurentLocalization.LaurentPolynomial K) where
  toFun x f := p2NegativeNativeChartToLaurent K m n f
    (p2NegativeNativeCechTermAddEquivSections K m n x f)
  map_zero' := by
    funext f
    simp
  map_add' x y := by
    funext f
    simp

/-- The actual canonical term's Laurent representation is injective. -/
theorem p2NegativeNativeCechTermToLaurent_injective (m n : ℕ) :
    Function.Injective (p2NegativeNativeCechTermToLaurent K m n) := by
  intro x y h
  apply (p2NegativeNativeCechTermAddEquivSections K m n).injective
  funext f
  apply p2NegativeNativeChartToLaurent_injective K m n f
  exact congrFun h f

/-- Every allowed negative-degree Laurent tuple comes from the SAME
canonical native Čech term; the section lifts are internally constructed. -/
theorem exists_p2NegativeNativeCechTermToLaurent_eq_of_support
    (m n : ℕ)
    (g : (Fin (n + 1) → Fin 3) → PlaneLaurentLocalization.LaurentPolynomial K)
    (hg : ∀ f a, a ∈ (g f).coeff.support →
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ x : (p2NegativeNativeCechComplex K m).X n,
      p2NegativeNativeCechTermToLaurent K m n x = g := by
  have hlift (f : Fin (n + 1) → Fin 3) :
      ∃ s : Γ(sheafOfModules PS m, p2CechBasicOpen K n f),
        p2NegativeNativeChartToLaurent K m n f s = g f :=
    exists_p2NegativeNativeChartToLaurent_eq_of_support K m n f (g f) (hg f)
  let s : ∀ f : Fin (n + 1) → Fin 3,
      Γ(sheafOfModules PS m, p2CechBasicOpen K n f) :=
    fun f => Classical.choose (hlift f)
  refine ⟨(p2NegativeNativeCechTermAddEquivSections K m n).symm s, ?_⟩
  funext f
  change p2NegativeNativeChartToLaurent K m n f
    (p2NegativeNativeCechTermAddEquivSections K m n
      ((p2NegativeNativeCechTermAddEquivSections K m n).symm s) f) = g f
  rw [AddEquiv.apply_symm_apply]
  exact Classical.choose_spec (hlift f)

/-- Actual term representatives have degree -m and the actual denominator
support, for all native canonical Čech degrees. -/
theorem p2NegativeNativeCechTermToLaurent_support
    (m n : ℕ) (x : (p2NegativeNativeCechComplex K m).X n)
    (f : Fin (n + 1) → Fin 3) :
    ∀ a ∈ (p2NegativeNativeCechTermToLaurent K m n x f).coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact p2NegativeNativeChartToLaurent_support K m n f
    (p2NegativeNativeCechTermAddEquivSections K m n x f)

end PfaffianDescent.ProjectivePlaneNative
