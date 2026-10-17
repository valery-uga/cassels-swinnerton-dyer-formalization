import PfaffianDescent.FourTangentFullBaseSchemeAlternative

/-! The finite-branch identification commutes with the INDEPENDENT actual
normalized product-dual immersion in ambient projective space. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def fourTangentDualToProjective (U : Fin 4 → Fin 4 → K) :
    Spec (.of (FourTangentDualAlgebra K)) ⟶
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :=
  fourTangentNormalizedEquationPoint U ⊥ (by
    intro p hp
    have hp0 : p = 0 := by simpa using hp
    subst p
    simp)

theorem fourTangentDualToProjective_isClosedImmersion
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0)
    (hn : ∀ i, ∃ j, U i j ≠ 0) :
    IsClosedImmersion (fourTangentDualToProjective U) :=
  linearNormalizedPointAt_isClosedImmersion _ _ _ _ _ _
    (fourTangentNormalizedCoordinates_surjective U hdiag hn)

/-- This factorization is derived from the actual normalized chart maps.
It is not an extra assumption comparing two projective configurations. -/
theorem fourTangentDualToFullBase_comp_ambient (U : Fin 4 → Fin 4 → K) :
    fourTangentDualToFullBase U ≫
      schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
        (fourTangentFullQuadraticBaseIdeal U) bot_le =
      fourTangentDualToProjective U := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
  let J := fourTangentFullQuadraticBaseIdeal U
  let x := fourTangentNormalizedCoordinates U
  have heI : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K (FourTangentDualAlgebra K)) x = 0 := by
    intro p hp
    have hp0 : p = 0 := by simpa [I] using hp
    subst p
    simp
  let heJ := fourTangentFullQuadraticBaseIdeal_evaluation_zero U
  let z := Ideal.Quotient.mk I.toIdeal (fourTangentChartLinearForm (K := K))
  let hz := polynomial_class_mem_grading I _ (fourTangentChartLinearForm_homogeneous (K := K))
  have hzOneI : (Ideal.Quotient.lift I.toIdeal (eval₂Hom
      (algebraMap K (FourTangentDualAlgebra K)) x) heI) z = 1 := by
    change aeval (R := K) (fourTangentNormalizedCoordinates U)
      (fourTangentChartLinearForm (K := K)) = 1
    exact fourTangentNormalizedLinearForm_eval U
  have hzOneJ : (Ideal.Quotient.lift J.toIdeal (eval₂Hom
      (algebraMap K (FourTangentDualAlgebra K)) x) heJ)
      (gradedQuotientMap I J bot_le z) = 1 := by
    change aeval (R := K) (fourTangentNormalizedCoordinates U)
      (fourTangentChartLinearForm (K := K)) = 1
    exact fourTangentNormalizedLinearForm_eval U
  exact linearNormalizedPointAt_comp_schemeQuotientMap I J bot_le x heI heJ
    z hz hzOneI hzOneJ

/-- Scheme-theoretic `B = Z` as an isomorphism with its specified canonical
map, together with the ambient identity of that very map. -/
theorem fourTangentFullQuadraticBase_embedded_alternative [IsAlgClosed K]
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hf : f ≠ 0) :
    (IsIso (fourTangentDualToFullBase (skewTangentDirections a b c d e f)) ∧
      fourTangentDualToFullBase (skewTangentDirections a b c d e f) ≫
        schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
          (fourTangentFullQuadraticBaseIdeal (skewTangentDirections a b c d e f))
          bot_le = fourTangentDualToProjective (skewTangentDirections a b c d e f)) ∨
      GroundTwistedCubicPresentation
        (fourTangentFullQuadraticBaseIdeal (skewTangentDirections a b c d e f)) := by
  rcases fourTangentFullQuadraticBase_scheme_alternative a b c d e f ha hb hc hd he hf
    with hIso | hTwisted
  · exact Or.inl ⟨hIso, fourTangentDualToFullBase_comp_ambient _⟩
  · exact Or.inr hTwisted

end PfaffianDescent.QuarticNet
