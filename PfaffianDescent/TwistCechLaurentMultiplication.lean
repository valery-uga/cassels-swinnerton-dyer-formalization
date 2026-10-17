import PfaffianDescent.TwistLaurentMultiplication
import PfaffianDescent.VoisinTwistCechFaceNaturality

/-! # Actual Cech multiplication in Laurent coordinates -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization TwistLaurent TwistCechTerms TwistCechTerms.GenericEvaluation
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The actual standard-cover cochain map induced by sheaf multiplication. -/
def p3NegativeTwistCechMultiplication (m d : ℕ) (q : PS d) :
    p3NegativeTwistCechComplex (K := K) (m + d) ⟶
      p3NegativeTwistCechComplex (K := K) m :=
  (CategoryTheory.cechComplexFunctor (p3StandardOpen (K := K))).map
    (mulHomogeneousPresheaf PS q m)

set_option backward.isDefEq.respectTransparency false in
theorem p3NegativeTwistCechMultiplication_projection
    (m d n : ℕ) (q : PS d) (f : Fin (n + 1) → Fin 4) :
    (p3NegativeTwistCechMultiplication K m d q).f n ≫
        Pi.π (p3CechTermFamily K m n) f =
      Pi.π (p3CechTermFamily K (m + d) n) f ≫
        (mulHomogeneousPresheaf PS q m).app
          (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a))) := by
  change (CategoryTheory.Limits.Pi.map fun f : Fin (n + 1) → Fin 4 =>
    (mulHomogeneousPresheaf PS q m).app
      (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a)))) ≫ _ = _
  simp only [CategoryTheory.Limits.Pi.map_π]

set_option backward.isDefEq.respectTransparency false in
theorem p3CechTermToBasic_mulHomogeneous
    (m d n : ℕ) (q : PS d) (f : Fin (n + 1) → Fin 4) :
    (mulHomogeneousPresheaf PS q m).app
        (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a))) ≫
      p3CechTermToBasic K m n f =
    p3CechTermToBasic K (m + d) n f ≫
      (mulHomogeneousPresheaf PS q m).app (op (cechBasicOpen K n f)) := by
  simp only [p3CechTermToBasic, Functor.mapIso_hom]
  rw [← Category.assoc, ← (mulHomogeneousPresheaf PS q m).naturality,
    Category.assoc, ← (mulHomogeneousPresheaf PS q m).naturality]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem p3CechTermComponentToLaurent_mulHomogeneous
    (m d n : ℕ) (q : PS d) (f : Fin (n + 1) → Fin 4)
    (s : p3CechTermFamily K (m + d) n f) :
    twistAwayToLaurent (K := K) m n f
        ((p3CechTermComponentIsoAway K m n f).hom
          ((mulHomogeneousPresheaf PS q m).app
            (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a))) s)) =
    polynomialToLaurent (K := K) (q : MvPolynomial (Fin 4) K) *
      twistAwayToLaurent (K := K) (m + d) n f
        ((p3CechTermComponentIsoAway K (m + d) n f).hom s) := by
  rw [p3CechTermComponentIsoAway_hom, p3CechTermComponentIsoAway_hom]
  have h := congrArg (fun t => t s) (p3CechTermToBasic_mulHomogeneous K m d n q f)
  simp only [ConcreteCategory.comp_apply] at h ⊢
  rw [h]
  exact chartAway_mulHomogeneous_toLaurent K n f m d q (f 0)
    (p3Coordinate_zero_dvd_cechDenominator (K := K) n f)
    ((p3CechTermToBasic K (m + d) n f) s)

set_option backward.isDefEq.respectTransparency false in
/-- Every component of actual Cech multiplication is literal Laurent
polynomial multiplication, including its twist shifts. -/
theorem p3NegativeTwistCechMultiplication_toLaurent
    (m d n : ℕ) (q : PS d)
    (x : (p3NegativeTwistCechComplex (K := K) (m + d)).X n)
    (f : Fin (n + 1) → Fin 4) :
    p3NegativeTwistCechTermToLaurent K m n
        ((p3NegativeTwistCechMultiplication K m d q).f n x) f =
      polynomialToLaurent (K := K) (q : MvPolynomial (Fin 4) K) *
        p3NegativeTwistCechTermToLaurent K (m + d) n x f := by
  change twistAwayToLaurent (K := K) m n f
    (p3NegativeTwistCechTermAddEquivAway K m n
      ((p3NegativeTwistCechMultiplication K m d q).f n x) f) = _
  rw [p3NegativeTwistCechTermAddEquivAway_apply]
  have h := congrArg (fun t => t x)
    (p3NegativeTwistCechMultiplication_projection K m d n q f)
  simp only [ConcreteCategory.comp_apply] at h
  calc
    _ = twistAwayToLaurent (K := K) m n f
        ((p3CechTermComponentIsoAway K m n f).hom
          ((mulHomogeneousPresheaf PS q m).app
            (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen (K := K) (f a)))
              ((Pi.π (p3CechTermFamily K (m + d) n) f) x))) :=
      congrArg (fun s => twistAwayToLaurent (K := K) m n f
        ((p3CechTermComponentIsoAway K m n f).hom s)) h
    _ = _ := by
      change _ = polynomialToLaurent (K := K) (q : MvPolynomial (Fin 4) K) *
        twistAwayToLaurent (K := K) (m + d) n f
          (p3NegativeTwistCechTermAddEquivAway K (m + d) n x f)
      rw [p3NegativeTwistCechTermAddEquivAway_apply]
      exact p3CechTermComponentToLaurent_mulHomogeneous K m d n q f _

end PfaffianDescent.ProjectiveNegativeTwist
