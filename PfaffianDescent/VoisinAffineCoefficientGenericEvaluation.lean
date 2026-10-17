import PfaffianDescent.VoisinAffineChartGenericEvaluation
import PfaffianDescent.SchemeAffineFunctions
import Mathlib.Algebra.MvPolynomial.Basic

/-! Generic residue-field evaluation respects the coefficient map of an
affine chart over a field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open MvPolynomial

universe u

theorem affineFunctionHom_genericFieldEvaluation
    {K F : Type u} [Field K] [Field F]
    (U : Scheme.{u})
    (s : Spec (.of F) ⟶ U)
    (t : U ⟶ Spec (.of K)) :
    ((Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom).comp
      (affineFunctionHom t) =
      (Spec.preimage (s ≫ t)).hom := by
  apply RingHom.ext
  intro r
  exact (specPreimage_comp_apply_eq_appTop_evaluation U s t r).symm

/-- The cubic coefficients specialize along the same field map as the
eight pulled chart sections. -/
theorem polynomial_genericFieldEvaluation
    {K F : Type u} [Field K] [Field F]
    (U : Scheme.{u})
    (s : Spec (.of F) ⟶ U)
    (t : U ⟶ Spec (.of K))
    (p : MvPolynomial (Fin 4) K) :
    (p.map (affineFunctionHom t)).map
        ((Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom) =
      p.map (Spec.preimage (s ≫ t)).hom := by
  rw [MvPolynomial.map_map, affineFunctionHom_genericFieldEvaluation]

end PfaffianDescent
