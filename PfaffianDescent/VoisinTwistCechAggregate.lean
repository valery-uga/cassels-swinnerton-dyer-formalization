import PfaffianDescent.VoisinAwayCechExact
import PfaffianDescent.VoisinTwistCechTerms
import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Aggregate coordinates on the projective-space Cech terms

This file packages each term of the raw standard-cover Cech complex of a
negative twist as a tuple of homogeneous localizations.  Composing with the
coordinate-independent Laurent embedding gives an injective additive map on
the entire Cech term and records its support condition.

The termwise localization equivalence is not asserted to intertwine the Cech
differential: its trivialization depends on the first coordinate of a tuple.
The Laurent map corrects this dependence and is the appropriate target for
the differential comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open scoped AddMonoidAlgebra BigOperators

universe u w

namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentLocalization TwistLaurent TwistCechTerms AwayCechExact

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The chosen categorical product of finitely many opens is their infimum. -/
lemma p3CechProduct_eq_inf (q : ℕ) (f : Fin (q + 1) → Fin 4) :
    (∏ᶜ fun a : Fin (q + 1) => p3StandardOpen (K := K) (f a)) =
      (⨅ a, p3StandardOpen (K := K) (f a)) := by
  apply le_antisymm
  · exact le_iInf fun a =>
      (Pi.π (fun a : Fin (q + 1) => p3StandardOpen (K := K) (f a)) a).le
  · exact (Pi.lift (fun a : Fin (q + 1) => homOfLE (iInf_le _ a))).le

/-- The underlying additive equivalence from a categorical product of
abelian groups to the corresponding dependent function type. -/
noncomputable def addCommGrpProductAddEquivPi {J : Type w}
    (A : J → AddCommGrpCat.{max u w}) :
    (∏ᶜ A : AddCommGrpCat) ≃+ (∀ j, A j) := by
  let e : (∏ᶜ A : AddCommGrpCat) ≅ AddCommGrpCat.of (∀ j, A j) :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor A))
      (AddCommGrpCat.HasLimit.productLimitCone A).isLimit
  exact
    { toFun := e.hom.hom
      invFun := e.inv.hom
      left_inv := fun x => CategoryTheory.congr_fun e.hom_inv_id x
      right_inv := fun x => CategoryTheory.congr_fun e.inv_hom_id x
      map_add' := fun x y => map_add e.hom.hom x y }

/-- Evaluation of the chosen product equivalence is the categorical product
projection. -/
lemma addCommGrpProductAddEquivPi_apply {J : Type w}
    (A : J → AddCommGrpCat.{max u w}) (x : (∏ᶜ A : AddCommGrpCat)) (j : J) :
    addCommGrpProductAddEquivPi A x j = (Pi.π A j) x := by
  let h := IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit (Discrete.functor A))
    (AddCommGrpCat.HasLimit.productLimitCone A).isLimit (Discrete.mk j)
  have hx := ConcreteCategory.congr_hom h x
  simpa [addCommGrpProductAddEquivPi,
    AddCommGrpCat.HasLimit.productLimitCone] using hx

/-- The additive equivalence underlying an isomorphism in `AddCommGrpCat`. -/
noncomputable def addCommGrpIsoAddEquiv {A B : AddCommGrpCat.{u}}
    (e : A ≅ B) : A ≃+ B where
  toFun := e.hom.hom
  invFun := e.inv.hom
  left_inv x := CategoryTheory.congr_fun e.hom_inv_id x
  right_inv x := CategoryTheory.congr_fun e.inv_hom_id x
  map_add' x y := map_add e.hom.hom x y

/-- The family of section groups which forms one term of the raw Cech
complex. -/
noncomputable abbrev p3CechTermFamily (m n : ℕ)
    (f : Fin (n + 1) → Fin 4) : AddCommGrpCat :=
  (modulePresheaf PS m).presheaf.obj
    (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a)))

/-- One summand of a raw Cech term, expressed as a homogeneous degree-zero
localization. -/
noncomputable def p3CechTermComponentIsoAway (m n : ℕ)
    (f : Fin (n + 1) → Fin 4) :
    p3CechTermFamily K m n f ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS
        (p3CechDenominator (K := K) n f)) :=
  (modulePresheaf PS m).presheaf.mapIso
      (eqToIso (p3CechProduct_eq_inf K n f)).op.symm ≪≫
    p3NegativeTwistCechSummandIsoAway K m n f

/-- A whole raw Cech term is additively equivalent to the tuple of its
homogeneous localization models. -/
noncomputable def p3NegativeTwistCechTermAddEquivAway (m n : ℕ) :
    (p3NegativeTwistCechComplex (K := K) m).X n ≃+
      AwayCochain K n :=
  (addCommGrpIsoAddEquiv
      (eqToIso (p3NegativeTwistCechComplex_X (K := K) m n))).trans
    ((addCommGrpProductAddEquivPi (p3CechTermFamily K m n)).trans
      (AddEquiv.piCongrRight fun f =>
        addCommGrpIsoAddEquiv (p3CechTermComponentIsoAway K m n f)))

/-- Evaluation of the aggregate localization model is projection to the
chosen Cech summand followed by its localization isomorphism. -/
lemma p3NegativeTwistCechTermAddEquivAway_apply
    (m n : ℕ) (x : (p3NegativeTwistCechComplex (K := K) m).X n)
    (f : Fin (n + 1) → Fin 4) :
    p3NegativeTwistCechTermAddEquivAway K m n x f =
      (p3CechTermComponentIsoAway K m n f).hom
        ((Pi.π (p3CechTermFamily K m n) f) x) := by
  change (p3CechTermComponentIsoAway K m n f).hom
      (addCommGrpProductAddEquivPi (p3CechTermFamily K m n)
        ((eqToIso (p3NegativeTwistCechComplex_X (K := K) m n)).hom x) f) = _
  rw [addCommGrpProductAddEquivPi_apply]
  congr 2

/-- The coordinate-independent Laurent model of an entire raw Cech term. -/
noncomputable def p3NegativeTwistCechTermToLaurent (m n : ℕ) :
    (p3NegativeTwistCechComplex (K := K) m).X n →+
      ((Fin (n + 1) → Fin 4) → LaurentLocalization.LaurentPolynomial K) where
  toFun x f := twistAwayToLaurent (K := K) m n f
    (p3NegativeTwistCechTermAddEquivAway K m n x f)
  map_zero' := by
    funext f
    simp
  map_add' x y := by
    funext f
    simp

/-- The aggregate Laurent model loses no information. -/
lemma p3NegativeTwistCechTermToLaurent_injective (m n : ℕ) :
    Function.Injective (p3NegativeTwistCechTermToLaurent K m n) := by
  intro x y h
  apply (p3NegativeTwistCechTermAddEquivAway K m n).injective
  funext f
  apply twistAwayToLaurent_injective (K := K) m n f
  exact congrFun h f

/-- A Laurent tuple with the correct twist degree and denominator support
lifts to the corresponding raw Cech term. -/
lemma exists_p3NegativeTwistCechTermToLaurent_eq_of_support
    (m n : ℕ)
    (g : (Fin (n + 1) → Fin 4) → LaurentLocalization.LaurentPolynomial K)
    (hg : ∀ f a, a ∈ (g f).coeff.support →
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ x : (p3NegativeTwistCechComplex (K := K) m).X n,
      p3NegativeTwistCechTermToLaurent K m n x = g := by
  have hlift (f : Fin (n + 1) → Fin 4) :
      ∃ z : HomogeneousLocalization.Away PS
          (p3CechDenominator (K := K) n f),
        twistAwayToLaurent (K := K) m n f z = g f :=
    exists_twistAwayToLaurent_eq_of_support (K := K) m n f (g f) (hg f)
  let z : AwayCochain K n := fun f => Classical.choose (hlift f)
  let x : (p3NegativeTwistCechComplex (K := K) m).X n :=
    (p3NegativeTwistCechTermAddEquivAway K m n).symm z
  refine ⟨x, ?_⟩
  funext f
  change twistAwayToLaurent (K := K) m n f
      (p3NegativeTwistCechTermAddEquivAway K m n x f) = g f
  rw [show p3NegativeTwistCechTermAddEquivAway K m n x = z by
    exact (p3NegativeTwistCechTermAddEquivAway K m n).apply_symm_apply z]
  exact Classical.choose_spec (hlift f)

/-- Every monomial in the aggregate Laurent image has twist degree `-m` and
can have negative exponents only among coordinates inverted by its tuple. -/
lemma p3NegativeTwistCechTermToLaurent_support_properties
    (m n : ℕ) (x : (p3NegativeTwistCechComplex (K := K) m).X n)
    (f : Fin (n + 1) → Fin 4) :
    ∀ a ∈ (p3NegativeTwistCechTermToLaurent K m n x f).coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact twistAwayToLaurent_support_properties (K := K) m n f
    (p3NegativeTwistCechTermAddEquivAway K m n x f)

end PfaffianDescent.ProjectiveNegativeTwist
