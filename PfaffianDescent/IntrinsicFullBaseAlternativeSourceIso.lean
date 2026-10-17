import PfaffianDescent.FourTangentIntrinsicFullBaseAlternative
import PfaffianDescent.IntrinsicQuadraticIdealPiece

/-! Source reconstruction preserves the full intrinsic base SCHEME and
its exact ambient embedding. No reduction of the source occurs. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def IntrinsicFullBaseEmbeddedAlternative
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) : Prop :=
  (∃ l : Z ⟶ scheme (intrinsicFullQuadraticBaseIdeal i),
    IsIso l ∧ l ≫ quotientProjMap (intrinsicFullQuadraticBaseIdeal i) = i) ∨
    GroundTwistedCubicPresentation (intrinsicFullQuadraticBaseIdeal i)

theorem intrinsicFullQuadraticBaseIdeal_comp_iso
    {K : Type u} [Field K] {Z Y : Scheme.{u}} (e : Z ≅ Y)
    (i : Y ⟶ Proj (homogeneousSubmodule (Fin 4) K)) :
    intrinsicFullQuadraticBaseIdeal (e.hom ≫ i) = intrinsicFullQuadraticBaseIdeal i := by
  apply HomogeneousIdeal.toIdeal_injective
  change Ideal.span (intrinsicFullQuadraticSystem (e.hom ≫ i) :
      Set (MvPolynomial (Fin 4) K)) =
    Ideal.span (intrinsicFullQuadraticSystem i : Set (MvPolynomial (Fin 4) K))
  rw [intrinsicFullQuadraticSystem_comp_isIso]

theorem intrinsicFullBase_embedded_alternative_precomp_iso
    {K : Type u} [Field K] {Z Y : Scheme.{u}} (e : Z ≅ Y)
    (i : Y ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (h : (∃ l : Y ⟶ scheme (intrinsicFullQuadraticBaseIdeal i),
      IsIso l ∧ l ≫ quotientProjMap (intrinsicFullQuadraticBaseIdeal i) = i) ∨
      GroundTwistedCubicPresentation (intrinsicFullQuadraticBaseIdeal i)) :
    (∃ l : Z ⟶ scheme (intrinsicFullQuadraticBaseIdeal (e.hom ≫ i)),
      IsIso l ∧ l ≫ quotientProjMap (intrinsicFullQuadraticBaseIdeal (e.hom ≫ i)) =
        e.hom ≫ i) ∨
      GroundTwistedCubicPresentation (intrinsicFullQuadraticBaseIdeal (e.hom ≫ i)) := by
  rw [intrinsicFullQuadraticBaseIdeal_comp_iso]
  rcases h with ⟨l, hl, hfac⟩ | hTwisted
  · letI := hl
    exact Or.inl ⟨e.hom ≫ l, inferInstance, by rw [Category.assoc, hfac]⟩
  · exact Or.inr hTwisted

end PfaffianDescent.QuarticNet
