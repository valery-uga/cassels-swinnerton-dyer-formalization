import PfaffianDescent.AffineRelativePolynomialPresentation309
import PfaffianDescent.NativeAffineHilbertClassification308

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- On an actual affine test Scheme, classification308 applies to the INTERNALLY
derived polynomial presentation. Both original test map and whole polynomial
family are retained. No classifying map, basis, frame or equality is an input. -/
theorem actualAffineRelativePoint_exists_classifyingMap309
    (R : Type u) [CommRing R] {S : Scheme.{u}} [IsAffine S]
    (f : S ⟶ Spec (.of R)) (m n : ℕ) (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197 (nativePolynomialProjection300 R m) (Over.mk f)) n) :
    letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
    ∃ g : MonomialFixedBaseHom308 R Γ(S, ⊤) m n,
      ∃ l : S ⟶ monomialCoefficientGluedScheme300 R m n,
        l ≫ monomialCoefficientGluedToBase300 R m n = f ∧
        l = S.isoSpec.hom ≫ g.val ∧
        actualAffineRelativePointOnPolynomialChart309 R f m n P =
          monomialFixedBasePointPullback308 R m n g := by
  letI : Algebra R Γ(S, ⊤) := actualAffineTestCoefficientAlgebra309 R f
  let Q := actualAffineRelativePointOnPolynomialChart309 R f m n P
  let g := nativeAffineHilbertPointClassifyingHom308 R m n hn Q
  refine ⟨g, S.isoSpec.hom ≫ g.val, ?_, rfl, ?_⟩
  · calc
      _ = S.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(S, ⊤))) := by
        rw [Category.assoc, g.property]
      _ = S.isoSpec.hom ≫ (S.isoSpec.inv ≫ f) :=
        congrArg (fun a => S.isoSpec.hom ≫ a) (actualAffineTestCoefficientSpecMap309 R f)
      _ = f := by simp only [Iso.hom_inv_id_assoc]
  · exact nativeAffineHilbertPointClassifyingHom_pullback308 R m n hn Q

end PfaffianDescent
end
