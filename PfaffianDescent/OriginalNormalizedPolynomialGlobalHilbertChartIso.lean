import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSchemeGlueData
import PfaffianDescent.OriginalNormalizedAffineClassifier317
import Mathlib.CategoryTheory.Yoneda

/-! The literal normalized polynomial model312 and the SAME internally chosen
positive coordinate chart parameter, compared in the ORIGINAL base slice.
No representability, chart comparison, base square or classifier equality is
supplied by the caller. All scheme tests and whole families are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u v w
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Small ordinary all-test Yoneda action cut, before the original geometric
objects and their dependent typeclass graphs are substituted. -/
private theorem originalYonedaRepresenterClassifier_comp001
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type w} {H J : C}
    (eta : F ≅ yoneda.obj H) (comparison : F ≅ G) (theta : G ≅ yoneda.obj J)
    (T : C) (Q : F.obj (.op T)) :
    eta.hom.app (.op T) Q ≫
        (Yoneda.fullyFaithful.preimageIso (eta.symm ≪≫ comparison ≪≫ theta)).hom =
      theta.hom.app (.op T) (comparison.hom.app (.op T) Q) := by
  have hCancel : eta.inv.app (.op T) (eta.hom.app (.op T) Q) = Q := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (eta.hom_inv_id_app (.op T)) Q
  have h := ConcreteCategory.congr_hom
    (congrArg (fun alpha => alpha.app (.op T))
      (Yoneda.fullyFaithful.map_preimage (eta.symm ≪≫ comparison ≪≫ theta).hom))
    (eta.hom.app (.op T) Q)
  change eta.hom.app (.op T) Q ≫
      (Yoneda.fullyFaithful.preimageIso (eta.symm ≪≫ comparison ≪≫ theta)).hom =
    theta.hom.app (.op T) (comparison.hom.app (.op T)
      (eta.inv.app (.op T) (eta.hom.app (.op T) Q))) at h
  rw [hCancel] at h
  exact h

variable {R : Type u} [CommRing R]
variable (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4)

/-- The actual original coordinate, regarded as a positive homogeneous
chart index. No new chart is selected. -/
def originalNormalizedCoordinateChartIndex001 :
    projectivePositiveHomogeneousChartIndex001 (grading (equationIdeal p hp)) :=
  ⟨coordinate (equationIdeal p hp) j, 1, by decide, coordinate_mem (equationIdeal p hp) j⟩

/-- Literal normalized polynomial Spec equals the actual coordinate open,
using the constructed polynomial presentation and native Proj chart iso. -/
def originalNormalizedPolynomialBasicOpenIso001 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 p j)) ≅
      (Proj.basicOpen (grading (equationIdeal p hp))
        (originalNormalizedCoordinateChartIndex001 p hp j).val).toScheme :=
  originalNormalizedHypersurfaceChartSpecIso312 p hp j ≪≫
    (Proj.basicOpenIsoSpec (grading (equationIdeal p hp))
      (coordinate (equationIdeal p hp) j) (coordinate_mem (equationIdeal p hp) j)
      (by decide : 0 < 1)).symm

/-- The comparison retains the literal original projective embedding. -/
theorem originalNormalizedPolynomialBasicOpenIso_embedding001 :
    (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom ≫
        (Proj.basicOpen (grading (equationIdeal p hp))
          (originalNormalizedCoordinateChartIndex001 p hp j).val).ι =
      originalNormalizedHypersurfaceChartEmbedding312 p hp j := by
  exact Category.assoc _ _ _

/-- The comparison is over the ORIGINAL coefficient ring. -/
theorem originalNormalizedPolynomialBasicOpenIso_overBase001 :
    (originalNormalizedPolynomialBasicOpenIso001 p hp j).hom ≫
        ((Proj.basicOpen (grading (equationIdeal p hp))
          (originalNormalizedCoordinateChartIndex001 p hp j).val).ι ≫
            toBase (equationIdeal p hp)) = originalNormalizedPolynomialFamily317 R p j := by
  calc
    _ = ((originalNormalizedPolynomialBasicOpenIso001 p hp j).hom ≫
        (Proj.basicOpen (grading (equationIdeal p hp))
          (originalNormalizedCoordinateChartIndex001 p hp j).val).ι) ≫
            toBase (equationIdeal p hp) := (Category.assoc _ _ _).symm
    _ = originalNormalizedHypersurfaceChartEmbedding312 p hp j ≫
        toBase (equationIdeal p hp) :=
      congrArg (fun f => f ≫ toBase (equationIdeal p hp))
        (originalNormalizedPolynomialBasicOpenIso_embedding001 p hp j)
    _ = Spec.map (CommRingCat.ofHom
        (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))) :=
      originalNormalizedHypersurfaceChartEmbedding_toBase312 p hp j
    _ = originalNormalizedPolynomialFamily317 R p j :=
      (originalNormalizedPolynomialFamily_toBase317 R p j).symm

/-- Actual entire-family functor comparison on ALL original-base tests. -/
def originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 (n : ℕ) :
    relativeFiniteFlatHilbertFunctor197 (originalNormalizedPolynomialFamily317 R p j) n ≅
      relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading (equationIdeal p hp))
          (originalNormalizedCoordinateChartIndex001 p hp j).val).ι ≫
            toBase (equationIdeal p hp)) n :=
  isomorphicOriginalFamilyHilbertFunctorIso001 _ _
    (originalNormalizedPolynomialBasicOpenIso001 p hp j)
    (originalNormalizedPolynomialBasicOpenIso_overBase001 p hp j) n

variable [IsNoetherianRing R] (n : ℕ) (hn : 0 < n)

/-- Yoneda compares the literal polynomial312 model to THIS SAME chosen H_Xj,
inside Over(Spec R). Both actual classifiers are internally constructed. -/
def originalNormalizedPolynomialChosenChartOverIso001 :
    monomialPolynomialContainmentRepresentingObject312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) ≅
      originalPositiveHomogeneousChartIndexRepresentingObject001
        (equationIdeal p hp) n hn (originalNormalizedCoordinateChartIndex001 p hp j) :=
  Yoneda.fullyFaithful.preimageIso
    ((polynomialHypersurfaceHilbertRepresentingIso312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) hn).symm ≪≫
      originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n ≪≫
      originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn
        (originalNormalizedCoordinateChartIndex001 p hp j))

/-- The exact slice isomorphism retains its ORIGINAL Spec R square. -/
theorem originalNormalizedPolynomialChosenChartOverIso_overBase001 :
    (originalNormalizedPolynomialChosenChartOverIso001 p hp j n hn).hom.left ≫
        (originalPositiveHomogeneousChartIndexRepresentingObject001 (equationIdeal p hp)
          n hn (originalNormalizedCoordinateChartIndex001 p hp j)).hom =
      (monomialPolynomialContainmentRepresentingObject312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j)).hom :=
  (originalNormalizedPolynomialChosenChartOverIso001 p hp j n hn).hom.w

/-- Exact classifier transformation, rather than an unstructured scheme iso. -/
theorem originalNormalizedPolynomialChosenChartOverIso_yoneda001 :
    yoneda.map (originalNormalizedPolynomialChosenChartOverIso001 p hp j n hn).hom =
      ((polynomialHypersurfaceHilbertRepresentingIso312 R 3 n
          (originalNormalizedHypersurfacePolynomial312 p j) hn).symm ≪≫
        originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n ≪≫
        originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn
          (originalNormalizedCoordinateChartIndex001 p hp j)).hom :=
  Yoneda.fullyFaithful.map_preimage _

/-- On every actual whole family, composing its literal polynomial classifier
with the constructed slice iso gives the chosen chart classifier. -/
theorem originalNormalizedPolynomialChosenChartOverIso_classifier001
    (T : Over (Spec (.of R)))
    (Q : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (originalNormalizedPolynomialFamily317 R p j) T) n) :
    (polynomialHypersurfaceHilbertRepresentingIso312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) hn).hom.app (.op T) Q ≫
        (originalNormalizedPolynomialChosenChartOverIso001 p hp j n hn).hom =
      (originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn
        (originalNormalizedCoordinateChartIndex001 p hp j)).hom.app (.op T)
          ((originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n).hom.app (.op T) Q) := by
  exact originalYonedaRepresenterClassifier_comp001
    (polynomialHypersurfaceHilbertRepresentingIso312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) hn)
    (originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn
      (originalNormalizedCoordinateChartIndex001 p hp j)) T Q

end PfaffianDescent
end
