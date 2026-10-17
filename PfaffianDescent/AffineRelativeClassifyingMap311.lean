import PfaffianDescent.AffineRelativeUniversalComparison311

/-! SOURCE ONLY311. Original affine test classification is derived from308
through the genuine presentation309. Naturality uses whole-point uniqueness,
not a requested equality of classifiers or a Γ-algebra-map certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)

lemma relativeFiniteFlatHilbertPoint_map_comp311 {X B : Scheme.{u}}
    (F : X ⟶ B) {T0 T1 T2 : Over B} (a : T0 ⟶ T1) (b : T1 ⟶ T2)
    (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T2) n) :
    (relativeFiniteFlatHilbertFunctor197 F n).map (a ≫ b).op P =
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op
        ((relativeFiniteFlatHilbertFunctor197 F n).map b.op P) := by
  apply Subtype.ext
  change P.val.comap (relativeHilbertAmbientMap197 F (a ≫ b)) =
    (P.val.comap (relativeHilbertAmbientMap197 F b)).comap
      (relativeHilbertAmbientMap197 F a)
  rw [relativeHilbertAmbientMap_comp197]
  exact P.val.comap_comp _ _

variable (T : Over (Spec (.of R))) [IsAffine T.left]

set_option backward.isDefEq.respectTransparency.types false in
/-- Every native affine slice map corresponds to its polynomial classifier. -/
lemma actualAffineRelativeUniversalPullback_onPolynomialChart_any311 :
    letI : Algebra R Γ(T.left, ⊤) := actualAffineTestCoefficientAlgebra309 R T.hom
    ∀ g : T ⟶ monomialCoefficientRepresentingObject309 R m n,
      actualAffineRelativePointOnPolynomialChart309 R T.hom m n
        (monomialRelativeUniversalPullback309 R m n T g) =
      monomialFixedBasePointPullback308 R m n
        ((actualAffineRelativeHomEquiv311 R T.hom m n).symm g) := by
  letI : Algebra R Γ(T.left, ⊤) := actualAffineTestCoefficientAlgebra309 R T.hom
  intro g
  have he := actualAffineRelativeUniversalPullback_onPolynomialChart311 R T.hom m n
    ((actualAffineRelativeHomEquiv311 R T.hom m n).symm g)
  simp only [Equiv.apply_symm_apply] at he
  apply Subtype.ext
  exact congrArg Subtype.val he

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual affine native universal pullback determines the full slice morphism. -/
lemma actualAffineRelativeUniversalPullback_injective311 :
    Function.Injective (monomialRelativeUniversalPullback309 R m n T) := by
  letI : Algebra R Γ(T.left, ⊤) := actualAffineTestCoefficientAlgebra309 R T.hom
  intro g h he
  have hp := congrArg (actualAffineRelativePointOnPolynomialChart309 R T.hom m n) he
  rw [actualAffineRelativeUniversalPullback_onPolynomialChart_any311,
    actualAffineRelativeUniversalPullback_onPolynomialChart_any311] at hp
  have hh := monomialFixedBasePointPullback_injective308 R m n hp
  exact (actualAffineRelativeHomEquiv311 R T.hom m n).symm.injective hh

/-- Canonical actual affine classifier; only the original point and n>0 enter. -/
def actualAffineRelativeClassifyingMap311 (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n) :
    T ⟶ monomialCoefficientRepresentingObject309 R m n := by
  letI : Algebra R Γ(T.left, ⊤) := actualAffineTestCoefficientAlgebra309 R T.hom
  exact (actualAffineRelativeHomEquiv311 R T.hom m n)
    (nativeAffineHilbertPointClassifyingHom308 R m n hn
      (actualAffineRelativePointOnPolynomialChart309 R T.hom m n P))

/-- Entire original affine point equals actual universal pullback, not just its support. -/
lemma actualAffineRelativeClassifyingMap_pullback311 (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T) n) :
    P = monomialRelativeUniversalPullback309 R m n T
      (actualAffineRelativeClassifyingMap311 R m n T hn P) := by
  letI : Algebra R Γ(T.left, ⊤) := actualAffineTestCoefficientAlgebra309 R T.hom
  apply actualAffineRelativePointOnPolynomialChart_injective311 R T.hom m n
  exact (nativeAffineHilbertPointClassifyingHom_pullback308 R m n hn
    (actualAffineRelativePointOnPolynomialChart309 R T.hom m n P)).trans
      (actualAffineRelativeUniversalPullback_onPolynomialChart311 R T.hom m n
        (nativeAffineHilbertPointClassifyingHom308 R m n hn
          (actualAffineRelativePointOnPolynomialChart309 R T.hom m n P))).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality for ANY native morphism between actual affine tests. -/
lemma actualAffineRelativeClassifyingMap_natural311
    {T0 T1 : Over (Spec (.of R))} [IsAffine T0.left] [IsAffine T1.left]
    (a : T0 ⟶ T1) (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) T1) n) :
    actualAffineRelativeClassifyingMap311 R m n T0 hn
      ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map a.op P) =
    a ≫ actualAffineRelativeClassifyingMap311 R m n T1 hn P := by
  apply actualAffineRelativeUniversalPullback_injective311 R m n T0
  exact (actualAffineRelativeClassifyingMap_pullback311 R m n T0 hn
      ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map
        a.op P)).symm.trans
    ((congrArg
      ((relativeFiniteFlatHilbertFunctor197 (nativePolynomialProjection300 R m) n).map a.op)
      (actualAffineRelativeClassifyingMap_pullback311 R m n T1 hn P)).trans
        (monomialRelativeUniversalPullback_natural309 R m n a
          (actualAffineRelativeClassifyingMap311 R m n T1 hn P)).symm)

end PfaffianDescent
end
