import PfaffianDescent.RelativeFiniteFlatHilbertFunctor197
import PfaffianDescent.MonomialCoefficientGlobalUniversalFamily300
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)

/-- SAME actually glued coefficient Scheme as a native object over original Spec R. -/
def monomialCoefficientRepresentingObject309 : Over (Spec (.of R)) :=
  Over.mk (monomialCoefficientGluedToBase300 R m n)

/-- Original global300 family is a point of the literal relative197 functor. -/
def monomialRelativeUniversalPoint309 :
    FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m)
        (monomialCoefficientRepresentingObject309 R m n)) n :=
  monomialCoefficientGlobalUniversalFamily300 R m n

/-- Canonical WHOLE universal pullback on an ARBITRARY original-base test Scheme. -/
def monomialRelativeUniversalPullback309 (T : Over (Spec (.of R)))
    (g : T ⟶ monomialCoefficientRepresentingObject309 R m n) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n :=
  (relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map
    g.op (monomialRelativeUniversalPoint309 R m n)

lemma monomialRelativeUniversalPullback_wholeIdeal309 (T : Over (Spec (.of R)))
    (g : T ⟶ monomialCoefficientRepresentingObject309 R m n) :
    (monomialRelativeUniversalPullback309 R m n T g).val =
      (monomialCoefficientUniversalWholeIdeal300 R m n).comap
        (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g) := rfl

/-- Arbitrary test morphisms preserve literal native universal pullback, not just support. -/
lemma monomialRelativeUniversalPullback_natural309
    {T0 T1 : Over (Spec (.of R))} (h : T0 ⟶ T1)
    (g : T1 ⟶ monomialCoefficientRepresentingObject309 R m n) :
    monomialRelativeUniversalPullback309 R m n T0 (h ≫ g) =
      (relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map h.op
        (monomialRelativeUniversalPullback309 R m n T1 g) := by
  apply Subtype.ext
  change (monomialCoefficientUniversalWholeIdeal300 R m n).comap
      (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) (h ≫ g)) =
    ((monomialCoefficientUniversalWholeIdeal300 R m n).comap
      (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) g)).comap
        (relativeHilbertAmbientMap197 (nativePolynomialProjection300 R m) h)
  rw [relativeHilbertAmbientMap_comp197]
  exact Scheme.IdealSheafData.comap_comp _ _ _

end PfaffianDescent
end
