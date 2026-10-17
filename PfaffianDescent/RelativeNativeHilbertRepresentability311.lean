import PfaffianDescent.RelativeGlobalClassifyingMap311
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic

/-! SOURCE ONLY311. Representation of the LITERAL finite-flat relative197
functor on ALL native scheme tests, for n>0, by the SAME actually glued H300.
No smoothness, hypersurface locus, genuine extra-LFP datum comparison, or n=0
claim is made. The inverse transformation is the original whole universal
family pullback, not a new point model. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (hn : 0 < n)

include hn in
/-- Genuine arbitrary-test classification equivalence. -/
def relativeNativeHilbertClassificationEquiv311 (T : Over (Spec (.of R))) :
    FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n ≃
    (T ⟶ monomialCoefficientRepresentingObject309 R m n) where
  toFun := relativeNativeGlobalClassifyingMap311 R m n T hn
  invFun := monomialRelativeUniversalPullback309 R m n T
  left_inv P := (relativeNativeGlobalClassifyingMap_pullback311 R m n T hn P).symm
  right_inv g := relativeNativeUniversalPullback_injective311 R m n T
    (relativeNativeGlobalClassifyingMap_pullback311 R m n T hn
      (monomialRelativeUniversalPullback309 R m n T g)).symm

include hn in
set_option backward.isDefEq.respectTransparency.types false in
/-- ALL native test morphisms preserve the classifier, derived from uniqueness. -/
lemma relativeNativeGlobalClassifyingMap_natural311
    {T0 T1 : Over (Spec (.of R))} (a : T0 ⟶ T1)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T1) n) :
    relativeNativeGlobalClassifyingMap311 R m n T0 hn
      ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map a.op P) =
    a ≫ relativeNativeGlobalClassifyingMap311 R m n T1 hn P := by
  apply relativeNativeUniversalPullback_injective311 R m n T0
  exact (relativeNativeGlobalClassifyingMap_pullback311 R m n T0 hn
      ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map
        a.op P)).symm.trans
    ((congrArg
      ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map a.op)
      (relativeNativeGlobalClassifyingMap_pullback311 R m n T1 hn P)).trans
        (monomialRelativeUniversalPullback_natural309 R m n a
          (relativeNativeGlobalClassifyingMap311 R m n T1 hn P)).symm)

include hn in
/-- SAME glued coefficient scheme represents the actual relative finite-flat
degree-n closed-subscheme functor on arbitrary original-base test schemes. -/
def relativeNativeHilbertRepresentingIso311 :
    relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n ≅
      yoneda.obj (monomialCoefficientRepresentingObject309 R m n) :=
  NatIso.ofComponents
    (fun T => (relativeNativeHilbertClassificationEquiv311 R m n hn T.unop).toIso)
    (by
      intro T0 T1 a
      apply ConcreteCategory.ext_apply
      intro P
      change relativeNativeGlobalClassifyingMap311 R m n T1.unop hn
          ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map a P) =
        a.unop ≫ relativeNativeGlobalClassifyingMap311 R m n T0.unop hn P
      exact relativeNativeGlobalClassifyingMap_natural311 R m n hn a.unop P)

include hn in
/-- The inverse of the genuine representing NatIso is literal whole universal pullback. -/
lemma relativeNativeHilbertRepresentingIso_inv_apply311
    (T : Over (Spec (.of R)))
    (g : T ⟶ monomialCoefficientRepresentingObject309 R m n) :
    (relativeNativeHilbertRepresentingIso311 R m n hn).inv.app (.op T) g =
      monomialRelativeUniversalPullback309 R m n T g := rfl

include hn in
/-- Literal whole-ideal identity of that inverse, on any scheme test. -/
lemma relativeNativeHilbertRepresentingIso_inv_wholeIdeal311
    (T : Over (Spec (.of R)))
    (g : T ⟶ monomialCoefficientRepresentingObject309 R m n) :
    ((relativeNativeHilbertRepresentingIso311 R m n hn).inv.app (.op T) g).val =
      (monomialCoefficientUniversalWholeIdeal300 R m n).comap
        (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g) := rfl

include hn in
/-- A literal original finite-flat family constructs a UNIQUE actual fixed-base
scheme morphism, with no classifier/overlap/representability outcome premise. -/
theorem originalRelativeFiniteFlatHilbertPoint_existsUnique_classifyingMap311
    (T : Over (Spec (.of R)))
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n) :
    ∃! g : T ⟶ monomialCoefficientRepresentingObject309 R m n,
      P = monomialRelativeUniversalPullback309 R m n T g := by
  refine ⟨relativeNativeGlobalClassifyingMap311 R m n T hn P,
    relativeNativeGlobalClassifyingMap_pullback311 R m n T hn P, ?_⟩
  intro g hg
  exact relativeNativeUniversalPullback_injective311 R m n T
    (hg.symm.trans (relativeNativeGlobalClassifyingMap_pullback311 R m n T hn P))

end PfaffianDescent
end
