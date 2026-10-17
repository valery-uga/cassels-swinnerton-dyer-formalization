import PfaffianDescent.QuarticExceptionalBaseLocus
import PfaffianDescent.QuarticTwistedCubicResidual
import PfaffianDescent.FiniteSchemeResidual
import PfaffianDescent.BinaryProjectiveLength

/-!
# Residual points in the exceptional `Δ = 0` branch

This joins the explicit exceptional twisted-cubic parametrization to the
degree-nine residual-point argument.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

variable {k : Type u} [Field k]

/-- The exceptional parametrization sends a degree-`n` homogeneous form to a
binary form of degree `3n`. -/
theorem exceptionalTwistedCubicParam_homogeneous
    (a b c d e : k) {F : MvPolynomial (Fin 4) k} {n : ℕ}
    (hF : F.IsHomogeneous n) :
    (exceptionalTwistedCubicParam a b c d e F).IsHomogeneous (3 * n) := by
  rw [exceptionalTwistedCubicParam_eq_coordinate_change]
  exact standardTwistedCubicParam_homogeneous (linearSubstitution_homogeneous _ hF)

/-- In the non-contained exceptional branch, the binary parameter-space
intersection of the twisted cubic with a cubic has finite rank nine. -/
theorem exceptional_param_cubic_intersection_isFinite [Infinite k]
    (a b c d e : k) (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0) :
    IsFinite (toBase (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF))) := by
  exact binary_projective_isFinite (exceptionalTwistedCubicParam a b c d e F)
    (exceptionalTwistedCubicParam_homogeneous a b c d e hF) hnonzero

/-- The checked rank calculation for the parameter-space degree-nine
intersection. -/
theorem exceptional_param_cubic_intersection_rank [Infinite k]
    (a b c d e : k) (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0)
    [IsFinite (toBase (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF)))] :
    AllCharacteristics.finiteSchemeRank
      (toBase (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
        (exceptionalTwistedCubicParam_homogeneous a b c d e hF))) = 9 := by
  have h := binary_projective_finiteSchemeRank
    (exceptionalTwistedCubicParam a b c d e F)
    (exceptionalTwistedCubicParam_homogeneous a b c d e hF) hnonzero
  simpa using h

/-- The image of the cubic Veronese under a linear coordinate change. -/
noncomputable def linearImageCubicVeronese
    (M : Matrix (Fin 4) (Fin 4) k) {A : Type u} [CommRing A] [Algebra k A]
    (s t : A) : Fin 4 → A :=
  fun i => ∑ j, algebraMap k A (M i j) * cubicVeronese s t j

theorem linearImageCubicVeronese_eval
    (M : Matrix (Fin 4) (Fin 4) k) {A : Type u} [CommRing A] [Algebra k A]
    (s t : A) (F : MvPolynomial (Fin 4) k) :
    aeval (linearImageCubicVeronese M s t) F =
      aeval (cubicVeronese s t) (linearSubstitution M F) := by
  have h : (aeval (cubicVeronese s t)).comp (linearSubstitution M) =
      aeval (linearImageCubicVeronese M s t) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, linearSubstitution_X, aeval_X]
    simp [linearImageCubicVeronese, linearCoordinate, Matrix.mulVec, dotProduct]
  exact (AlgHom.congr_fun h F).symm

/-- Evaluation of the explicit exceptional parametrization is evaluation on
the corresponding linear image of the standard cubic Veronese. -/
theorem exceptionalTwistedCubicParam_eval
    (a b c d e : k) {A : Type u} [CommRing A] [Algebra k A]
    (s t : A) (F : MvPolynomial (Fin 4) k) :
    aeval ![s, t] (exceptionalTwistedCubicParam a b c d e F) =
      aeval (linearImageCubicVeronese
        (baseLocusCubicCoefficientMatrix a b c d e) s t) F := by
  rw [exceptionalTwistedCubicParam_eq_coordinate_change]
  change aeval ![s, t]
      (standardTwistedCubicParam k
        (linearSubstitution (baseLocusCubicCoefficientMatrix a b c d e) F)) = _
  rw [standardTwistedCubicParam_eval]
  exact (linearImageCubicVeronese_eval
    (baseLocusCubicCoefficientMatrix a b c d e) s t F).symm

/-- In the exceptional full-support branch, a cubic containing the quartic
dual point of the explicit twisted cubic has a rational point. -/
theorem cubic_point_of_exceptional_twisted_cubic_double_point
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    {L : Type u} [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (r w : L) (hw : w ≠ 0) (hr : (minpoly k r).natDegree = 4)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hjet : aeval ![(1 : DualNumber L),
      TrivSqZeroExt.inl r + TrivSqZeroExt.inr w]
      (exceptionalTwistedCubicParam a b c d e F) = 0) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ aeval x F = 0 := by
  have hbe : b * e - c * d ≠ 0 :=
    baseLocus_be_sub_cd_ne_zero_of_delta_zero a b c d e f hb hc hd he hdelta
  have hM : IsUnit (baseLocusCubicCoefficientMatrix a b c d e).det :=
    isUnit_iff_ne_zero.mpr
      (baseLocusCubicCoefficientMatrix_det_ne_zero a b c d e ha hb hc hd he hbe)
  apply cubic_point_of_coordinate_changed_twisted_cubic_double_point
    (baseLocusCubicCoefficientMatrix a b c d e) hM r w hw hr F hF
  rw [← linearImageCubicVeronese_eval, ← exceptionalTwistedCubicParam_eval]
  exact hjet

/-- The non-contained exceptional branch reduces to an actual finite
intersection: a rank-nine ground subscheme of the cubic containing the
rank-eight tangent jet has a rank-one residual, hence a rational section.
No split parametrization of the exceptional base curve is required here. -/
theorem cubic_section_of_rank_nine_exceptional_intersection
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {X Z : Scheme.{u}}
    (c : X ⟶ hypersurface F hF)
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsFinite (c ≫ hypersurfaceToBase F hF)]
    (hX : AllCharacteristics.finiteSchemeRank (c ≫ hypersurfaceToBase F hF) = 9)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase F hF) = 8) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  obtain ⟨s, hs⟩ := finite_scheme_residual_section_of_codimension_one i
    (c ≫ hypersurfaceToBase F hF) 8 hX
    (by simpa only [Category.assoc] using hZ)
  exact ⟨s ≫ finiteClosedResidualι i _ ≫ c,
    by simpa only [Category.assoc] using hs⟩

end QuarticNet
end PfaffianDescent
