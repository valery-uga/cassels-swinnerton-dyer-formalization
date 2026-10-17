import PfaffianDescent.VoisinProjectiveSpaceCech
import PfaffianDescent.VoisinTwistLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped AddMonoidAlgebra BigOperators
universe u
namespace PfaffianDescent.TwistCechTerms

open LaurentLocalization TwistLaurent
open ProjectiveNegativeTwist

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

abbrev LaurentExponent := LaurentLocalization.LaurentExponent
abbrev LaurentPolynomial := LaurentLocalization.LaurentPolynomial K

def cechSummandToLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    Γ(sheafOfModules PS m, ⨅ a, p3StandardOpen (K := K) (f a)) →+
      LaurentPolynomial K where
  toFun s := twistAwayToLaurent (K := K) m n f
    ((p3NegativeTwistCechSummandIsoAway K m n f).hom s)
  map_zero' := by simp
  map_add' x y := by simp

lemma cechSummandToLaurent_injective
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    Function.Injective (cechSummandToLaurent (K := K) m n f) := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso
    (p3NegativeTwistCechSummandIsoAway K m n f).hom).1
  exact twistAwayToLaurent_injective (K := K) m n f h

lemma cechSummandToLaurent_support_properties
    (m n : ℕ) (f : Fin (n + 1) → Fin 4)
    (s : Γ(sheafOfModules PS m, ⨅ a, p3StandardOpen (K := K) (f a))) :
    ∀ a ∈ (cechSummandToLaurent (K := K) m n f s).coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact twistAwayToLaurent_support_properties (K := K) m n f
    ((p3NegativeTwistCechSummandIsoAway K m n f).hom s)

lemma exists_cechSummandToLaurent_eq_of_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) (g : LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ s : Γ(sheafOfModules PS m, ⨅ a, p3StandardOpen (K := K) (f a)),
      cechSummandToLaurent (K := K) m n f s = g := by
  obtain ⟨z, hz⟩ := exists_twistAwayToLaurent_eq_of_support (K := K) m n f g hg
  refine ⟨(p3NegativeTwistCechSummandIsoAway K m n f).inv z, ?_⟩
  change twistAwayToLaurent (K := K) m n f
      ((p3NegativeTwistCechSummandIsoAway K m n f).hom
        ((p3NegativeTwistCechSummandIsoAway K m n f).inv z)) = g
  rw [Iso.inv_hom_id_apply]
  exact hz

end PfaffianDescent.TwistCechTerms
