import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear
import PfaffianDescent.CubicCanonicalTraceScalarDiagram

/-! # Actual base constants and negative-twist multiplication on Proj -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of an actual base constant is its homogeneous fraction at every
projective point. This follows from the checked degree-zero section action. -/
theorem projectiveBaseConstant_fraction
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (c : K) (x : Proj (grading I)) :
    ((affineFunctionHom (toBase I) c).1 ⟨x, trivial⟩).val =
      algebraMap (CoordinateRing I) (Fiber (grading I) x)
        (algebraMap K (CoordinateRing I) c) := by
  letI := projectiveGlobalSectionsAlgebra I
  have h := positiveGlobalSection_eval_smul_degree I 0 c (1 : grading I 0)
  have he := congrArg (fun s => s.1 ⟨x, trivial⟩) h
  change Localization.mk
      (((c • (1 : grading I 0) : grading I 0) : CoordinateRing I)) 1 =
    ((affineFunctionHom (toBase I) c).1 ⟨x, trivial⟩).val *
      Localization.mk (1 : CoordinateRing I) 1 at he
  have hc : ((c • (1 : grading I 0) : grading I 0) : CoordinateRing I) =
      algebraMap K (CoordinateRing I) c := by
    change c • (1 : CoordinateRing I) = _
    exact (Algebra.smul_def c (1 : CoordinateRing I)).trans (mul_one _)
  have hmk : (Localization.mk (1 : CoordinateRing I)
      (1 : (positivePointIdeal (grading I) x).primeCompl) :
      PositiveFiber (grading I) x) = 1 := by
    exact (Localization.mk_one_eq_algebraMap 1).trans (map_one _)
  have hleft : (Localization.mk
      (((c • (1 : grading I 0) : grading I 0) : CoordinateRing I))
      (1 : (positivePointIdeal (grading I) x).primeCompl) :
      PositiveFiber (grading I) x) =
      algebraMap (CoordinateRing I) (PositiveFiber (grading I) x)
        (algebraMap K (CoordinateRing I) c) :=
    (congrArg (fun a : CoordinateRing I =>
      (Localization.mk a (1 : (positivePointIdeal (grading I) x).primeCompl) :
        PositiveFiber (grading I) x)) hc).trans (Localization.mk_one_eq_algebraMap _)
  have hright : ((affineFunctionHom (toBase I) c).1 ⟨x, trivial⟩).val *
      (Localization.mk (1 : CoordinateRing I)
        (1 : (positivePointIdeal (grading I) x).primeCompl) :
        PositiveFiber (grading I) x) =
      ((affineFunctionHom (toBase I) c).1 ⟨x, trivial⟩).val :=
    (congrArg (fun a : PositiveFiber (grading I) x =>
      ((affineFunctionHom (toBase I) c).1 ⟨x, trivial⟩).val * a) hmk).trans (mul_one _)
  exact hright.symm.trans (he.symm.trans hleft)

set_option backward.isDefEq.respectTransparency false in
/-- The actual cubic constant coefficient morphism acts on every section by the
restriction of the actual base-field constant. -/
theorem cubicScalarHomogeneous_app_eq_base_constant_smul
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (c : K)
    (m : ℕ) (U : (Proj (grading (equationIdeal p hp))).Opens)
    (y : (sheafOfModules (grading (equationIdeal p hp)) m).val.obj (op U)) :
    (mulHomogeneous (grading (equationIdeal p hp))
      (cubicScalarHomogeneous K p hp c) m).val.app (op U) y =
      schemeOpenBaseRingHom (hypersurfaceToBase p hp) U c • y := by
  apply Subtype.ext
  funext x
  change algebraMap (CoordinateRing (equationIdeal p hp))
      (Fiber (grading (equationIdeal p hp)) x.1)
      (algebraMap K (CoordinateRing (equationIdeal p hp)) c) * y.1 x =
    ((affineFunctionHom (toBase (equationIdeal p hp)) c).1
      ⟨x.1, trivial⟩).val * y.1 x
  rw [projectiveBaseConstant_fraction]

end PfaffianDescent.ProjectiveNegativeTwist
