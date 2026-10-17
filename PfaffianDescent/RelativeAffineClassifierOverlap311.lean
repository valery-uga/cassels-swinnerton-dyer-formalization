import PfaffianDescent.AffineRelativeClassifyingMap311
import PfaffianDescent.RelativeHilbertTestCoverUniqueness309
import Mathlib.AlgebraicGeometry.Gluing

/-! SOURCE ONLY311. The test's own affine cover is chosen internally. Its
intersections need NOT be affine: their own genuine affine covers reflect
equality of the actual classifying maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (T : Over (Spec (.of R))) (hn : 0 < n)
variable (P : FiniteFlatHilbertPoint195
  (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n)

set_option backward.isDefEq.respectTransparency.types false in
/-- This is the ORIGINAL cover component; no affineness premise is added. -/
private instance relativeNativeAffineCoverComponent_isAffine311
    (i : T.left.affineCover.I₀) :
    IsAffine (relativeHilbertTestCoverObject309 T T.left.affineCover i).left := by
  change IsAffine (T.left.affineCover.X i)
  infer_instance

/-- SAME original finite-flat point restricted by the native197 functor. -/
def relativeNativeAffineChartPoint311 (i : T.left.affineCover.I₀) :
    FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m)
        (relativeHilbertTestCoverObject309 T T.left.affineCover i)) n :=
  (relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map
    (relativeHilbertTestCoverMap309 T T.left.affineCover i).op P

include hn P in
def relativeNativeAffineChartClassifier311 (i : T.left.affineCover.I₀) :
    relativeHilbertTestCoverObject309 T T.left.affineCover i ⟶
      monomialCoefficientRepresentingObject309 R m n :=
  actualAffineRelativeClassifyingMap311 R m n
    (relativeHilbertTestCoverObject309 T T.left.affineCover i) hn
    (relativeNativeAffineChartPoint311 R m n T P i)

include hn P in
def relativeNativeAffineChartSchemeMap311 (i : T.left.affineCover.I₀) :
    T.left.affineCover.X i ⟶ monomialCoefficientGluedScheme300 R m n :=
  (relativeNativeAffineChartClassifier311 R m n T hn P i).left

include hn P in
lemma relativeNativeAffineChartClassifier_pullback311 (i : T.left.affineCover.I₀) :
    relativeNativeAffineChartPoint311 R m n T P i =
      monomialRelativeUniversalPullback309 R m n
        (relativeHilbertTestCoverObject309 T T.left.affineCover i)
        (relativeNativeAffineChartClassifier311 R m n T hn P i) :=
  actualAffineRelativeClassifyingMap_pullback311 R m n
    (relativeHilbertTestCoverObject309 T T.left.affineCover i) hn _

include hn P in
lemma relativeNativeAffineChartSchemeMap_toBase311 (i : T.left.affineCover.I₀) :
    relativeNativeAffineChartSchemeMap311 R m n T hn P i ≫
      monomialCoefficientGluedToBase300 R m n = T.left.affineCover.f i ≫ T.hom :=
  Over.w (relativeNativeAffineChartClassifier311 R m n T hn P i)

include hn P in
set_option backward.isDefEq.respectTransparency.types false in
/-- WHOLE overlap equality is DERIVED using affine refinements of the genuine
test-cover pullbacks. No separatedness, intersection-affineness, compatibility
or equal-classifier hypothesis is added to the original point. -/
lemma relativeNativeAffineChartSchemeMap_compatible311
    (i j : T.left.affineCover.I₀) :
    pullback.fst (T.left.affineCover.f i) (T.left.affineCover.f j) ≫
      relativeNativeAffineChartSchemeMap311 R m n T hn P i =
    pullback.snd (T.left.affineCover.f i) (T.left.affineCover.f j) ≫
      relativeNativeAffineChartSchemeMap311 R m n T hn P j := by
  let U := T.left.affineCover
  let W := pullback (U.f i) (U.f j)
  apply W.affineCover.hom_ext
  intro k
  let Z : Over (Spec (.of R)) :=
    Over.mk (W.affineCover.f k ≫ pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ T.hom)
  letI : IsAffine Z.left := by
    change IsAffine (W.affineCover.X k)
    infer_instance
  let a : Z ⟶ relativeHilbertTestCoverObject309 T U i :=
    Over.homMk (W.affineCover.f k ≫ pullback.fst (U.f i) (U.f j))
      (by
        change (W.affineCover.f k ≫ pullback.fst (U.f i) (U.f j)) ≫
          (U.f i ≫ T.hom) =
          W.affineCover.f k ≫ pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ T.hom
        exact Category.assoc _ _ _)
  let b : Z ⟶ relativeHilbertTestCoverObject309 T U j :=
    Over.homMk (W.affineCover.f k ≫ pullback.snd (U.f i) (U.f j))
      (by
        change (W.affineCover.f k ≫ pullback.snd (U.f i) (U.f j)) ≫
          (U.f j ≫ T.hom) =
          W.affineCover.f k ≫ pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ T.hom
        simp only [Category.assoc]
        rw [← pullback.condition_assoc])
  have hab : a ≫ relativeHilbertTestCoverMap309 T U i =
      b ≫ relativeHilbertTestCoverMap309 T U j := by
    apply Over.OverMorphism.ext
    change (W.affineCover.f k ≫ pullback.fst (U.f i) (U.f j)) ≫ U.f i =
      (W.affineCover.f k ≫ pullback.snd (U.f i) (U.f j)) ≫ U.f j
    simp only [Category.assoc]
    rw [pullback.condition]
  have hpoints :
      (relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map a.op
        (relativeNativeAffineChartPoint311 R m n T P i) =
      (relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map b.op
        (relativeNativeAffineChartPoint311 R m n T P j) := by
    change (relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map a.op
        ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map
          (relativeHilbertTestCoverMap309 T U i).op P) =
      (relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map b.op
        ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map
          (relativeHilbertTestCoverMap309 T U j).op P)
    rw [← relativeFiniteFlatHilbertPoint_map_comp311,
      ← relativeFiniteFlatHilbertPoint_map_comp311, hab]
  have ha := actualAffineRelativeClassifyingMap_natural311 R m n a hn
    (relativeNativeAffineChartPoint311 R m n T P i)
  have hb := actualAffineRelativeClassifyingMap_natural311 R m n b hn
    (relativeNativeAffineChartPoint311 R m n T P j)
  have hmaps : a ≫ relativeNativeAffineChartClassifier311 R m n T hn P i =
      b ≫ relativeNativeAffineChartClassifier311 R m n T hn P j :=
    ha.symm.trans ((congrArg (actualAffineRelativeClassifyingMap311 R m n Z hn)
      hpoints).trans hb)
  have hleft := congrArg (fun q : Z ⟶ monomialCoefficientRepresentingObject309 R m n =>
    q.left) hmaps
  change (W.affineCover.f k ≫ pullback.fst (U.f i) (U.f j)) ≫
      relativeNativeAffineChartSchemeMap311 R m n T hn P i =
    (W.affineCover.f k ≫ pullback.snd (U.f i) (U.f j)) ≫
      relativeNativeAffineChartSchemeMap311 R m n T hn P j at hleft
  simpa only [Category.assoc] using hleft

end PfaffianDescent
end
