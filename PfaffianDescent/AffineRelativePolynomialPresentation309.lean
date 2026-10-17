import PfaffianDescent.NativeAmbientPullbackChart300
import PfaffianDescent.NativePolynomialScalarScheme300
import PfaffianDescent.RelativeHilbertFamily197
import PfaffianDescent.FiniteFlatHilbertTestPoints195
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] {S : Scheme.{u}} [IsAffine S]
variable (f : S ⟶ Spec (.of R)) (m : ℕ)

/-- Canonical original-base algebra of the ACTUAL affine test's whole section ring. -/
def actualAffineTestCoefficientAlgebra309 : Algebra R Γ(S, ⊤) :=
  (Spec.preimage (S.isoSpec.inv ≫ f)).hom.toAlgebra

lemma actualAffineTestCoefficientSpecMap309 :
    letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(S, ⊤))) = S.isoSpec.inv ≫ f := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  exact Spec.map_preimage (S.isoSpec.inv ≫ f)

/-- Actual polynomial-spectrum map into the SAME native relative197 ambient. -/
def actualAffineRelativePolynomialChartMap309 :
    Spec (.of (MvPolynomial (Fin m) Γ(S, ⊤))) ⟶
      pullback f (nativePolynomialProjection300 R m) := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  exact nativeAmbientChartLift300 f (nativePolynomialProjection300 R m) S.isoSpec.inv
    (Spec.map (CommRingCat.ofHom (algebraMap R Γ(S, ⊤))))
    (actualAffineTestCoefficientSpecMap309 R f).symm
    (nativePolynomialScalarMap300 R Γ(S, ⊤) m)
    (nativePolynomialProjection300 Γ(S, ⊤) m)
    (nativePolynomialScalar_isPullback300 R Γ(S, ⊤) m)

lemma actualAffineRelativePolynomialChartMap_toTest309 :
    actualAffineRelativePolynomialChartMap309 R f m ≫
      relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f) =
    nativePolynomialProjection300 Γ(S, ⊤) m ≫ S.isoSpec.inv := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  exact nativeAmbientChartLift_fst300 _ _ _ _ _ _ _ _

lemma actualAffineRelativePolynomialChartMap_isPullback309 :
    IsPullback (actualAffineRelativePolynomialChartMap309 R f m)
      (nativePolynomialProjection300 Γ(S, ⊤) m)
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f))
      S.isoSpec.inv := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  exact nativeAmbientChartLift_isPullback300 _ _ _ _ _ _ _ _

/-- Isomorphism is DERIVED by base change of the actual affine presentation Iso. -/
def actualAffineRelativePolynomialAmbientIso309 :
    Spec (.of (MvPolynomial (Fin m) Γ(S, ⊤))) ≅
      pullback f (nativePolynomialProjection300 R m) := by
  letI : IsIso (actualAffineRelativePolynomialChartMap309 R f m) :=
    (actualAffineRelativePolynomialChartMap_isPullback309 R f m).isIso_fst_of_isIso
  exact asIso (actualAffineRelativePolynomialChartMap309 R f m)

/-- Native whole point in polynomial coordinates, ready for ORIGINAL308 classification. -/
def actualAffineRelativePointOnPolynomialChart309 (n : ℕ)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f)) n) :
    FiniteFlatHilbertPoint195 (nativePolynomialProjection300 Γ(S, ⊤) m) n :=
  finiteFlatHilbertBaseChange195 (actualAffineRelativePolynomialChartMap309 R f m)
    (nativePolynomialProjection300 Γ(S, ⊤) m)
    (relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f))
    S.isoSpec.inv (actualAffineRelativePolynomialChartMap_isPullback309 R f m) n P

lemma actualAffineRelativePointOnPolynomialChart_wholeIdeal309 (n : ℕ)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f)) n) :
    (actualAffineRelativePointOnPolynomialChart309 R f m n P).val =
      P.val.comap (actualAffineRelativePolynomialChartMap309 R f m) := rfl

end PfaffianDescent
end
