import AllCharacteristics.DisjointFiniteSubschemeUnion
import AllCharacteristics.FiniteSubschemeRank

/-!
# Disjoint unions of finite-subscheme data

This packages the affine presentations attached canonically to finite-subscheme
data into the existing scheme-theoretic disjoint-union construction.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

/-- Two finite-subscheme data with disjoint canonical affine presentations have
a finite-subscheme datum of the summed rank. -/
noncomputable def finiteSubschemeDatumOfTwoDisjointData
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {m n : ℕ} (D₁ : FiniteSubschemeDatum f m) (D₂ : FiniteSubschemeDatum f n)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁))
      (Set.range (finiteSubschemeDatumSpecMap f D₂))) :
    FiniteSubschemeDatum f (m + n) := by
  letI : IsFinite (D₁.val.subschemeι ≫ f) := D₁.property.1
  letI : IsFinite (D₂.val.subschemeι ≫ f) := D₂.property.1
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₂.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₂.val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfDisjointSpecUnion f
    (finiteSubschemeDatumSpecMap f D₁)
    (finiteSubschemeDatumSpecMap f D₂)
    (finiteSubschemeDatumSpecMap_toBase f D₁)
    (finiteSubschemeDatumSpecMap_toBase f D₂)
    m n
    (finiteSubschemeDatumSpecMap_finrank f D₁)
    (finiteSubschemeDatumSpecMap_finrank f D₂)
    h₁₂

/-- Three finite-subscheme data whose canonical affine presentations are
successively disjoint have a finite-subscheme datum of the summed rank. -/
noncomputable def finiteSubschemeDatumOfThreeDisjointData
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {m n p : ℕ} (D₁ : FiniteSubschemeDatum f m)
    (D₂ : FiniteSubschemeDatum f n) (D₃ : FiniteSubschemeDatum f p)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁))
      (Set.range (finiteSubschemeDatumSpecMap f D₂)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap (finiteSubschemeDatumSpecMap f D₁)
        (finiteSubschemeDatumSpecMap f D₂)))
      (Set.range (finiteSubschemeDatumSpecMap f D₃))) :
    FiniteSubschemeDatum f (m + n + p) := by
  letI : IsFinite (D₁.val.subschemeι ≫ f) := D₁.property.1
  letI : IsFinite (D₂.val.subschemeι ≫ f) := D₂.property.1
  letI : IsFinite (D₃.val.subschemeι ≫ f) := D₃.property.1
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₂.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₃.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₂.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₃.val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfThreeDisjointSpecUnion f
    (finiteSubschemeDatumSpecMap f D₁)
    (finiteSubschemeDatumSpecMap f D₂)
    (finiteSubschemeDatumSpecMap f D₃)
    (finiteSubschemeDatumSpecMap_toBase f D₁)
    (finiteSubschemeDatumSpecMap_toBase f D₂)
    (finiteSubschemeDatumSpecMap_toBase f D₃)
    m n p
    (finiteSubschemeDatumSpecMap_finrank f D₁)
    (finiteSubschemeDatumSpecMap_finrank f D₂)
    (finiteSubschemeDatumSpecMap_finrank f D₃)
    h₁₂ h₁₂₃

/-- A degree-ten datum and two degree-three data with disjoint canonical
presentations combine to a degree-sixteen finite-subscheme datum. -/
noncomputable def finiteSubschemeDatum_rankSixteenOfDegreeTenAndTwoDegreeThree
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (D₁₀ : FiniteSubschemeDatum f 10)
    (D₃ : FiniteSubschemeDatum f 3) (D₃' : FiniteSubschemeDatum f 3)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap (finiteSubschemeDatumSpecMap f D₁₀)
        (finiteSubschemeDatumSpecMap f D₃)))
      (Set.range (finiteSubschemeDatumSpecMap f D₃'))) :
    FiniteSubschemeDatum f 16 := by
  simpa using finiteSubschemeDatumOfThreeDisjointData f D₁₀ D₃ D₃' h₁₂ h₁₂₃

/-- The finite datum obtained from three successively disjoint components has
support exactly equal to the union of the component supports. -/
theorem range_finiteSubschemeDatumSpecMap_finiteSubschemeDatumOfThreeDisjointData
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {m n p : ℕ} (D₁ : FiniteSubschemeDatum f m)
    (D₂ : FiniteSubschemeDatum f n) (D₃ : FiniteSubschemeDatum f p)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁))
      (Set.range (finiteSubschemeDatumSpecMap f D₂)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap (finiteSubschemeDatumSpecMap f D₁)
        (finiteSubschemeDatumSpecMap f D₂)))
      (Set.range (finiteSubschemeDatumSpecMap f D₃))) :
    Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfThreeDisjointData f D₁ D₂ D₃ h₁₂ h₁₂₃)) =
      Set.range (finiteSubschemeDatumSpecMap f D₁) ∪
        Set.range (finiteSubschemeDatumSpecMap f D₂) ∪
          Set.range (finiteSubschemeDatumSpecMap f D₃) := by
  letI : IsFinite (D₁.val.subschemeι ≫ f) := D₁.property.1
  letI : IsFinite (D₂.val.subschemeι ≫ f) := D₂.property.1
  letI : IsFinite (D₃.val.subschemeι ≫ f) := D₃.property.1
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₂.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₃.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₂.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₃.val.subschemeι ≫ f)
  unfold finiteSubschemeDatumOfThreeDisjointData
  convert range_finiteSubschemeDatumSpecMap_finiteSubschemeDatumOfThreeDisjointSpecUnion f
      (finiteSubschemeDatumSpecMap f D₁) (finiteSubschemeDatumSpecMap f D₂)
      (finiteSubschemeDatumSpecMap f D₃)
      (finiteSubschemeDatumSpecMap_toBase f D₁)
      (finiteSubschemeDatumSpecMap_toBase f D₂)
      (finiteSubschemeDatumSpecMap_toBase f D₃)
      m n p
      (finiteSubschemeDatumSpecMap_finrank f D₁)
      (finiteSubschemeDatumSpecMap_finrank f D₂)
      (finiteSubschemeDatumSpecMap_finrank f D₃)
      h₁₂ h₁₂₃ using 1 <;> rfl

end AllCharacteristics
