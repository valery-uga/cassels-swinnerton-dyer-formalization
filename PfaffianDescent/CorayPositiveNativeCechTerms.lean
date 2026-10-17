import PfaffianDescent.CorayPositiveNativeChartLaurentRealization
import PfaffianDescent.VoisinTwistCechAggregate

/-! Native terms of the CANONICAL positive-twist coordinate-cover Čech complex.
No comparison equivalence or cohomology statement is supplied as a premise.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open LaurentLocalization TwistLaurent TwistCechTerms
open TwistCechTerms.GenericEvaluation
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The actual Mathlib Čech complex of the SAME positive-twist presheaf
on the original four coordinate opens. -/
def p3PositiveNativeCechComplex (m : ℕ) : CochainComplex AddCommGrpCat ℕ :=
  (CategoryTheory.cechComplexFunctor (p3StandardOpen (K := K))).obj
    (positiveSheafOfModules PS m).presheaf

/-- The actual canonical categorical section factor of one native term. -/
abbrev p3PositiveNativeCechTermFamily (m n : ℕ)
    (f : Fin (n + 1) → Fin 4) : AddCommGrpCat :=
  (positiveSheafOfModules PS m).presheaf.obj
    (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a)))

/-- Only equality of the OWN canonical opens is used to present a native
categorical term factor as native sections on its denominator basic open. -/
def p3PositiveNativeCechComponentIsoBasic (m n : ℕ)
    (f : Fin (n + 1) → Fin 4) :
    p3PositiveNativeCechTermFamily K m n f ≅
      Γ(positiveSheafOfModules PS m, cechBasicOpen K n f) :=
  (positiveSheafOfModules PS m).presheaf.mapIso
    (eqToIso ((p3CechProduct_eq_inf K n f).trans
      (p3CechBasicOpen_eq_inf (K := K) n f).symm)).op.symm

/-- Every actual canonical term is the family of its OWN native section
factors, through the existing categorical product projections. -/
def p3PositiveNativeCechTermAddEquivSections (m n : ℕ) :
    (p3PositiveNativeCechComplex K m).X n ≃+
      (∀ f : Fin (n + 1) → Fin 4,
        Γ(positiveSheafOfModules PS m, cechBasicOpen K n f)) :=
  (addCommGrpProductAddEquivPi (p3PositiveNativeCechTermFamily K m n)).trans
    (AddEquiv.piCongrRight fun f =>
      addCommGrpIsoAddEquiv (p3PositiveNativeCechComponentIsoBasic K m n f))

/-- Evaluation is the actual product projection followed by the actual
native open-equality map; this fixes the comparison map explicitly. -/
theorem p3PositiveNativeCechTermAddEquivSections_apply
    (m n : ℕ) (x : (p3PositiveNativeCechComplex K m).X n)
    (f : Fin (n + 1) → Fin 4) :
    p3PositiveNativeCechTermAddEquivSections K m n x f =
      (p3PositiveNativeCechComponentIsoBasic K m n f).hom
        ((Pi.π (p3PositiveNativeCechTermFamily K m n) f) x) := by
  change (p3PositiveNativeCechComponentIsoBasic K m n f).hom
    (addCommGrpProductAddEquivPi (p3PositiveNativeCechTermFamily K m n) x f) = _
  exact congrArg
    (fun y : p3PositiveNativeCechTermFamily K m n f =>
      (p3PositiveNativeCechComponentIsoBasic K m n f).hom y)
    (addCommGrpProductAddEquivPi_apply
      (p3PositiveNativeCechTermFamily K m n)
      (show (∏ᶜ p3PositiveNativeCechTermFamily K m n : AddCommGrpCat) from x) f)

/-- The canonical positive-twist Čech term has its actual restored Laurent
representatives, formed from its OWN native sections. -/
def p3PositiveNativeCechTermToLaurent (m n : ℕ) :
    (p3PositiveNativeCechComplex K m).X n →+
      ((Fin (n + 1) → Fin 4) → LaurentLocalization.LaurentPolynomial K) where
  toFun x f := p3PositiveNativeChartToLaurent K m n f
    (p3PositiveNativeCechTermAddEquivSections K m n x f)
  map_zero' := by
    funext f
    simp
  map_add' x y := by
    funext f
    simp

/-- The actual canonical term's Laurent representation is injective. -/
theorem p3PositiveNativeCechTermToLaurent_injective (m n : ℕ) :
    Function.Injective (p3PositiveNativeCechTermToLaurent K m n) := by
  intro x y h
  apply (p3PositiveNativeCechTermAddEquivSections K m n).injective
  funext f
  apply p3PositiveNativeChartToLaurent_injective K m n f
  exact congrFun h f

/-- Every allowed positive-degree Laurent tuple comes from the SAME
canonical native Čech term; the section lifts are internally constructed. -/
theorem exists_p3PositiveNativeCechTermToLaurent_eq_of_support
    (m n : ℕ)
    (g : (Fin (n + 1) → Fin 4) → LaurentLocalization.LaurentPolynomial K)
    (hg : ∀ f a, a ∈ (g f).coeff.support →
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ x : (p3PositiveNativeCechComplex K m).X n,
      p3PositiveNativeCechTermToLaurent K m n x = g := by
  have hlift (f : Fin (n + 1) → Fin 4) :
      ∃ s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n f),
        p3PositiveNativeChartToLaurent K m n f s = g f :=
    exists_p3PositiveNativeChartToLaurent_eq_of_support K m n f (g f) (hg f)
  let s : ∀ f : Fin (n + 1) → Fin 4,
      Γ(positiveSheafOfModules PS m, cechBasicOpen K n f) :=
    fun f => Classical.choose (hlift f)
  refine ⟨(p3PositiveNativeCechTermAddEquivSections K m n).symm s, ?_⟩
  funext f
  change p3PositiveNativeChartToLaurent K m n f
    (p3PositiveNativeCechTermAddEquivSections K m n
      ((p3PositiveNativeCechTermAddEquivSections K m n).symm s) f) = g f
  rw [AddEquiv.apply_symm_apply]
  exact Classical.choose_spec (hlift f)

/-- Actual term representatives have degree +m and the actual denominator
support, for all native canonical Čech degrees. -/
theorem p3PositiveNativeCechTermToLaurent_support
    (m n : ℕ) (x : (p3PositiveNativeCechComplex K m).X n)
    (f : Fin (n + 1) → Fin 4) :
    ∀ a ∈ (p3PositiveNativeCechTermToLaurent K m n x f).coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact p3PositiveNativeChartToLaurent_support K m n f
    (p3PositiveNativeCechTermAddEquivSections K m n x f)

end PfaffianDescent.ProjectiveNegativeTwist
