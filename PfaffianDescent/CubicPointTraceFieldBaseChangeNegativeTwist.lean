import PfaffianDescent.CubicPointTraceFieldBaseChangeGradedTwistIso
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal
import AllCharacteristics.ProjectiveBaseChange

/-! # Actual negative twists on a coefficient-extended cubic

The coefficient morphism is the proved actual scheme-theoretic scalar
extension of the cubic. Its pullback identifies every native negative twist.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K L : Type u} [Field K] [Field L] (g : K →+* L)
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)

/-- The actual cubic coefficient map, whose Cartesian base-change square is
proved by `isPullback_projectiveCoefficientMap`. -/
def cubicPointTraceFieldBaseChangeCubicCoefficientMap :
    hypersurface (p.map g) (hp.map g) ⟶ hypersurface p hp :=
  projectiveCoefficientMap g (equationIdeal p hp)
    (equationIdeal (p.map g) (hp.map g)) (equationIdeal_map g p hp)

/-- Every actual native negative twist pulls back to the actual native twist
of the coefficient-extended cubic, with no identification hypothesis. -/
def cubicPointTraceFieldBaseChangeCubicNegativeTwistIso (m : ℕ) :
    (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) m) ≅
      sheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) m := by
  let I := equationIdeal p hp
  let J := equationIdeal (p.map g) (hp.map g)
  exact cubicPointTraceFieldBaseChangeGradedTwistPullbackIso
    (grading I) (grading J) (gradedCoefficientMap g I J (equationIdeal_map g p hp))
    (irrelevant_le_map_gradedCoefficientMap g I J (equationIdeal_map g p hp))
    (gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small)
    (gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 4) L) (grading J)
      (quotientGradedRingHom J) (quotientGradedRingHom_surjective J)
      mvPolynomial_irrelevant_le_span_degreeOne_small) m

/-- The actual coefficient map is an actual scalar-extension projection,
through the canonical hypersurface base-change isomorphism. -/
theorem cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection :
    (hypersurfaceBaseChangeIso g p hp).hom ≫
      pullback.fst (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom g)) =
        cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp :=
  projectiveBaseChangeIso_hom_fst g (equationIdeal p hp)
    (equationIdeal (p.map g) (hp.map g)) (equationIdeal_map g p hp)

/-- The actual cubic coefficient extension is flat. -/
instance cubicPointTraceFieldBaseChangeCubicCoefficientMap_flat :
    Flat (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp) := by
  rw [← cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection]
  infer_instance

end PfaffianDescent.ProjectiveNegativeTwist
