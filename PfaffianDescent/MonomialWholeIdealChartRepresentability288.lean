import PfaffianDescent.MonomialWholeIdealChartNaturality287
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda

/-! An actual categorical representability statement for one monomial
whole-ideal chart. Chart data retain the entire ideal and its genuine
monomial basis condition; no Hilbert representation is assumed. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory Opposite
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)

def monomialWholeIdealChartFunctor288 (hk : B k = 0) :
    CommAlgCat.{u} R ⥤ Type u where
  obj A := MonomialWholeIdealChart287 (A := A) B
  map f := TypeCat.ofHom (monomialWholeIdealChartMap287 B k hk f.hom.toRingHom)
  map_id A := by
    ext x
    change monomialWholeIdealChartMap287 B k hk (RingHom.id A) x = x
    exact monomialWholeIdealChartMap_id287 B k hk x
  map_comp f g := by
    ext x
    change monomialWholeIdealChartMap287 B k hk (g.hom.toRingHom.comp f.hom.toRingHom) x =
      monomialWholeIdealChartMap287 B k hk g.hom.toRingHom
        (monomialWholeIdealChartMap287 B k hk f.hom.toRingHom x)
    exact monomialWholeIdealChartMap_comp287 B k hk f.hom.toRingHom g.hom.toRingHom x

def monomialCyclicCoefficientObject288 : CommAlgCat.{u} R :=
  CommAlgCat.of R (UniversalCyclicCoefficientAlgebra282 R m n B k)

def monomialCyclicCoefficientChartEquiv288 (hk : B k = 0) (A : CommAlgCat.{u} R) :
    (monomialCyclicCoefficientObject288 R m n B k ⟶ A) ≃
      MonomialWholeIdealChart287 (A := A) B where
  toFun f := cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk f.hom
  invFun x := CommAlgCat.ofHom
    ((cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk).symm x)
  left_inv f := by
    apply CommAlgCat.hom_ext
    exact (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk).left_inv f.hom
  right_inv x := (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk).right_inv x

/-- The original cyclic coefficient algebra represents this entire-ideal
chart on commutative R-algebras, naturally under arbitrary algebra maps. -/
def monomialCyclicCoefficientChartNatIso288 (hk : B k = 0) :
    coyoneda.obj (.op (monomialCyclicCoefficientObject288 R m n B k)) ≅
      monomialWholeIdealChartFunctor288 R m n B k hk := by
  refine NatIso.ofComponents
    (fun A => (monomialCyclicCoefficientChartEquiv288 R m n B k hk A).toIso) ?_
  intro A D f
  ext p
  change cyclicCoefficientWholeIdealChartEquiv287 (A := D) B k R hk
      (f.hom.comp p.hom) =
    monomialWholeIdealChartMap287 B k hk f.hom.toRingHom
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p.hom)
  exact cyclicCoefficientWholeIdealChartEquiv_natural287 (A := A) (E := D)
    B k R hk p.hom f.hom

end PfaffianDescent
