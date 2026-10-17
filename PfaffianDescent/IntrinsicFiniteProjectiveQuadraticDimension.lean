import PfaffianDescent.IntrinsicFiniteProjectiveQuadraticFieldExtension
import PfaffianDescent.IntrinsicFullQuadraticBaseDimensionInfinite
import AllCharacteristics.FiniteSchemeBaseChangeRank
import Mathlib.FieldTheory.RatFunc.Basic

/-! Arbitrary-field dimension three for the full quadratic system of the
ACTUAL arbitrary finite rank-eight closed subscheme with finite full base.
No singleton support, chosen ground chart, or supplied triple is needed. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem intrinsicFullQuadraticSystem_finrank_three_of_finite_base_any_field
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))] :
    finrank k (intrinsicFullQuadraticSystem i) = 3 := by
  let K := RatFunc k
  letI : Infinite K :=
    Infinite.of_injective (algebraMap (Polynomial k) (RatFunc k))
      (RatFunc.algebraMap_injective k)
  let q := canonicalProjectiveFieldBaseChangeEmbedding (K := K) i
  letI : IsClosedImmersion q := canonicalProjectiveFieldBaseChangeEmbedding_isClosedImmersion i
  letI : IsFinite (q ≫ ambientToBase) := canonicalProjectiveFieldBaseChangeEmbedding_isFinite i
  let eB := intrinsicFullQuadraticBaseActualFieldExtensionIso (K := K) i
  letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal q)) := by
    rw [← intrinsicFullQuadraticBaseActualFieldExtensionIso_toField (K := K) i]
    infer_instance
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let t := i ≫ ambientToBase (R := k)
  have hbase : (pullbackSymmetry b t).hom ≫ pullback.snd t b =
      q ≫ ambientToBase := by
    rw [pullbackSymmetry_hom_comp_snd, canonicalProjectiveFieldBaseChangeEmbedding_toField]
  have hnew : AllCharacteristics.finiteSchemeRank (q ≫ ambientToBase) = 8 :=
    (AllCharacteristics.finiteSchemeRank_eq_of_field_baseChange t b
      (q ≫ ambientToBase) (pullbackSymmetry b t) hbase).symm.trans hZ
  have hd := intrinsicFullQuadraticSystem_finrank_eq_three_of_finite_base q hnew
  exact (intrinsicFullQuadraticSystem_actual_fieldExtension_finrank (K := K) i).symm.trans hd

end PfaffianDescent
