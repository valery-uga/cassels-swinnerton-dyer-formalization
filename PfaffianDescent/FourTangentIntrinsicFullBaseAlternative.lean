import PfaffianDescent.FourTangentIntrinsicQuadraticSystem

/-! The actual scheme-theoretic base of |I_Z(2)| for the specified four
tangent double points is Z itself or an embedded twisted cubic. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem exists_ambientIsoLift_of_ideal_eq
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (B J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (h : B = J)
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (l : Z ⟶ scheme J) (hl : IsIso l) (hfac : l ≫ quotientProjMap J = i) :
    ∃ f : Z ⟶ scheme B, IsIso f ∧ f ≫ quotientProjMap B = i := by
  subst J
  exact ⟨l, hl, hfac⟩

/-- Literal intrinsic-base form of the geometric base-locus lemma. Every
quadratic in the ideal sheaf of the actual supplied embedding is included;
the four double points keep their nilpotent directions in the finite branch. -/
theorem fourTangent_intrinsicFullQuadraticBase_embedded_alternative
    {K : Type u} [Field K] [IsAlgClosed K]
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    let U := skewTangentDirections a b c d e f
    let q := fourTangentDualToProjective U ≫ quotientProjMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    let B := intrinsicFullQuadraticBaseIdeal q
    (∃ l : Spec (.of (FourTangentDualAlgebra K)) ⟶ scheme B,
      IsIso l ∧ l ≫ quotientProjMap B = q) ∨
      GroundTwistedCubicPresentation B := by
  let U := skewTangentDirections a b c d e f
  let q := fourTangentDualToProjective U ≫ quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  let B := intrinsicFullQuadraticBaseIdeal q
  let J := fourTangentFullQuadraticBaseIdeal U
  have hBJ : B = J := fourTangent_intrinsicFullQuadraticBaseIdeal_eq U
    (skewTangentDirections_diagonal_zero a b c d e f)
  rcases fourTangentFullQuadraticBase_embedded_alternative a b c d e f
      ha hb hc hd he hf with ⟨hIso, hEmbed⟩ | hTwisted
  · apply Or.inl
    have hAmbient : fourTangentDualToFullBase U ≫ quotientProjMap J = q := by
      rw [← schemeQuotientMap_comp_quotientProjMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) J bot_le,
        ← Category.assoc]
      exact congrArg (fun t => t ≫ quotientProjMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))) hEmbed
    exact exists_ambientIsoLift_of_ideal_eq B J hBJ q
      (fourTangentDualToFullBase U) hIso hAmbient
  · apply Or.inr
    change GroundTwistedCubicPresentation B
    rw [hBJ]
    exact hTwisted

end PfaffianDescent.QuarticNet
