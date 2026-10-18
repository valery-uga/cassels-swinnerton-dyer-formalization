import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Explicit coefficient extension on fraction fields.
All polynomial variables are retained; no specialization is performed. -/

noncomputable section
namespace AllCharacteristics
universe u v w

/-- The fraction-field map extending an injective map of integral domains. -/
def fractionRingMapOfInjective
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Injective f) :
    FractionRing A →+* FractionRing B :=
  IsFractionRing.lift (K := FractionRing A)
    (g := (algebraMap B (FractionRing B)).comp f)
    ((IsFractionRing.injective B (FractionRing B)).comp hf)

@[simp] theorem fractionRingMapOfInjective_algebraMap
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Injective f) (a : A) :
    fractionRingMapOfInjective f hf (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (f a) := by
  simp only [fractionRingMapOfInjective, IsFractionRing.lift_algebraMap,
    RingHom.comp_apply]

theorem fractionRingMapOfInjective_injective
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (fractionRingMapOfInjective f hf) :=
  (fractionRingMapOfInjective f hf).injective

/-- Extension of coefficients on a rational function field. Its map on
polynomials is the coefficient map, and its map on every variable is identity. -/
def mvFractionCoefficientMap
    {k : Type u} {l : Type v} [Field k] [Field l] (σ : Type w) (f : k →+* l) :
    FractionRing (MvPolynomial σ k) →+* FractionRing (MvPolynomial σ l) :=
  fractionRingMapOfInjective (MvPolynomial.map f)
    (MvPolynomial.map_injective f f.injective)

theorem mvFractionCoefficientMap_injective
    {k : Type u} {l : Type v} [Field k] [Field l] (σ : Type w) (f : k →+* l) :
    Function.Injective (mvFractionCoefficientMap σ f) :=
  (mvFractionCoefficientMap σ f).injective

@[simp] theorem mvFractionCoefficientMap_algebraMap
    {k : Type u} {l : Type v} [Field k] [Field l] (σ : Type w) (f : k →+* l)
    (p : MvPolynomial σ k) :
    mvFractionCoefficientMap σ f
        (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) p) =
      algebraMap (MvPolynomial σ l) (FractionRing (MvPolynomial σ l))
        (p.map f) := by
  exact fractionRingMapOfInjective_algebraMap _ _ _

@[simp] theorem mvFractionCoefficientMap_X
    {k : Type u} {l : Type v} [Field k] [Field l] (σ : Type w) (f : k →+* l) (i : σ) :
    mvFractionCoefficientMap σ f
        (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
          (MvPolynomial.X i)) =
      algebraMap (MvPolynomial σ l) (FractionRing (MvPolynomial σ l))
        (MvPolynomial.X i) := by
  rw [mvFractionCoefficientMap_algebraMap, MvPolynomial.map_X]

@[simp] theorem mvFractionCoefficientMap_C
    {k : Type u} {l : Type v} [Field k] [Field l] (σ : Type w) (f : k →+* l) (a : k) :
    mvFractionCoefficientMap σ f
        (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))
          (MvPolynomial.C a)) =
      algebraMap (MvPolynomial σ l) (FractionRing (MvPolynomial σ l))
        (MvPolynomial.C (f a)) := by
  rw [mvFractionCoefficientMap_algebraMap, MvPolynomial.map_C]

@[simp] theorem mvFractionCoefficientMap_base
    {k : Type u} {l : Type v} [Field k] [Field l] (σ : Type w) (f : k →+* l) (a : k) :
    mvFractionCoefficientMap σ f (algebraMap k (FractionRing (MvPolynomial σ k)) a) =
      algebraMap l (FractionRing (MvPolynomial σ l)) (f a) := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial σ k)
    (FractionRing (MvPolynomial σ k)),
    IsScalarTower.algebraMap_apply l (MvPolynomial σ l)
      (FractionRing (MvPolynomial σ l))]
  exact mvFractionCoefficientMap_C σ f a

theorem mvFractionCoefficientMap_comp_base
    {k : Type u} {l : Type v} [Field k] [Field l] (σ : Type w) (f : k →+* l) :
    (mvFractionCoefficientMap σ f).comp
        (algebraMap k (FractionRing (MvPolynomial σ k))) =
      (algebraMap l (FractionRing (MvPolynomial σ l))).comp f := by
  ext a
  exact mvFractionCoefficientMap_base σ f a

end AllCharacteristics
