import PfaffianDescent.RelativeAffineClassifierOverlap311

/-! SOURCE ONLY311. Genuine global classifying map assembled by the native
open-cover gluing theorem from compatibility DERIVED in the predecessor.
The original whole finite-flat point is recovered by genuine cover uniqueness. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (T : Over (Spec (.of R))) (hn : 0 < n)
variable (P : FiniteFlatHilbertPoint195
  (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n)

include hn P in
def relativeNativeGlobalClassifyingSchemeMap311 :
    T.left ⟶ monomialCoefficientGluedScheme300 R m n :=
  T.left.affineCover.glueMorphisms
    (relativeNativeAffineChartSchemeMap311 R m n T hn P)
    (relativeNativeAffineChartSchemeMap_compatible311 R m n T hn P)

include hn P in
lemma relativeNativeGlobalClassifyingSchemeMap_chart311 (i : T.left.affineCover.I₀) :
    T.left.affineCover.f i ≫ relativeNativeGlobalClassifyingSchemeMap311 R m n T hn P =
      relativeNativeAffineChartSchemeMap311 R m n T hn P i :=
  T.left.affineCover.ι_glueMorphisms _ _ i

include hn P in
set_option backward.isDefEq.respectTransparency.types false in
lemma relativeNativeGlobalClassifyingSchemeMap_toBase311 :
    relativeNativeGlobalClassifyingSchemeMap311 R m n T hn P ≫
      monomialCoefficientGluedToBase300 R m n = T.hom := by
  apply T.left.affineCover.hom_ext
  intro i
  rw [← Category.assoc, relativeNativeGlobalClassifyingSchemeMap_chart311]
  exact relativeNativeAffineChartSchemeMap_toBase311 R m n T hn P i

include hn P in
/-- Actual map in the native slice category, on an arbitrary original test. -/
def relativeNativeGlobalClassifyingMap311 :
    T ⟶ monomialCoefficientRepresentingObject309 R m n :=
  Over.homMk (relativeNativeGlobalClassifyingSchemeMap311 R m n T hn P)
    (relativeNativeGlobalClassifyingSchemeMap_toBase311 R m n T hn P)

include hn P in
lemma relativeNativeGlobalClassifyingMap_chart311 (i : T.left.affineCover.I₀) :
    relativeHilbertTestCoverMap309 T T.left.affineCover i ≫
        relativeNativeGlobalClassifyingMap311 R m n T hn P =
      relativeNativeAffineChartClassifier311 R m n T hn P i := by
  apply Over.OverMorphism.ext
  exact relativeNativeGlobalClassifyingSchemeMap_chart311 R m n T hn P i

include hn P in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original arbitrary-test point is EXACTLY the whole universal ideal pullback.
No local basis/affine-cover compatibility/representability equality is supplied. -/
lemma relativeNativeGlobalClassifyingMap_pullback311 :
    P = monomialRelativeUniversalPullback309 R m n T
      (relativeNativeGlobalClassifyingMap311 R m n T hn P) := by
  apply relativeHilbertPoint_eq_of_affineRestrictions309
    (nativePolynomialProjection300 R m) T n
  intro i
  change relativeNativeAffineChartPoint311 R m n T P i =
    (relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map
      (relativeHilbertTestCoverMap309 T T.left.affineCover i).op
      (monomialRelativeUniversalPullback309 R m n T
        (relativeNativeGlobalClassifyingMap311 R m n T hn P))
  rw [← monomialRelativeUniversalPullback_natural309,
    relativeNativeGlobalClassifyingMap_chart311]
  exact relativeNativeAffineChartClassifier_pullback311 R m n T hn P i

set_option backward.isDefEq.respectTransparency.types false in
/-- Whole universal pullbacks reflect arbitrary-test native slice maps. -/
lemma relativeNativeUniversalPullback_injective311 :
    Function.Injective (monomialRelativeUniversalPullback309 R m n T) := by
  intro g h he
  apply Over.OverMorphism.ext
  apply T.left.affineCover.hom_ext
  intro i
  letI : IsAffine (relativeHilbertTestCoverObject309 T T.left.affineCover i).left := by
    change IsAffine (T.left.affineCover.X i)
    infer_instance
  let c := relativeHilbertTestCoverMap309 T T.left.affineCover i
  have hp := congrArg
    ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map c.op) he
  rw [← monomialRelativeUniversalPullback_natural309,
    ← monomialRelativeUniversalPullback_natural309] at hp
  have hh := actualAffineRelativeUniversalPullback_injective311 R m n
    (relativeHilbertTestCoverObject309 T T.left.affineCover i) hp
  exact congrArg (fun q : relativeHilbertTestCoverObject309 T T.left.affineCover i ⟶
    monomialCoefficientRepresentingObject309 R m n => q.left) hh

end PfaffianDescent
end
