import PfaffianDescent.QuarticExceptionalParameter
import PfaffianDescent.QuarticNetKoszul

/-!
# The exceptional base locus is a twisted cubic

The three cleared-denominator quadrics in the `Δ = 0` branch generate the
kernel of the binary-cubic parametrization.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

variable {K : Type*} [Field K]

theorem scaledBaseLocusQuadricPolynomials_independent (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    LinearIndependent K (scaledBaseLocusQuadricPolynomials a b c d e f) := by
  rw [Fintype.linearIndependent_iff]
  intro q hq i
  have hcoeff (j l : Fin 4) := congrArg (coeff (Finsupp.single j 1 + Finsupp.single l 1)) hq
  fin_cases i
  · have h := hcoeff 1 2
    simp +decide [scaledBaseLocusQuadricPolynomials, scaledBaseLocusQuadrics,
      offDiagonalQuadric, Fin.sum_univ_three, coeff_smul, X, C_mul', monomial_mul,
      coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply] at h
    exact h.resolve_right (not_or.mpr ⟨ha, hb⟩)
  · have h := hcoeff 1 3
    simp +decide [scaledBaseLocusQuadricPolynomials, scaledBaseLocusQuadrics,
      offDiagonalQuadric, Fin.sum_univ_three, coeff_smul, X, C_mul', monomial_mul,
      coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply] at h
    exact h.resolve_right (not_or.mpr ⟨ha, hc⟩)
  · have h := hcoeff 2 3
    simp +decide [scaledBaseLocusQuadricPolynomials, scaledBaseLocusQuadrics,
      offDiagonalQuadric, Fin.sum_univ_three, coeff_smul, X, C_mul', monomial_mul,
      coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply] at h
    exact h.resolve_right (not_or.mpr ⟨hb, hc⟩)

theorem exceptionalTwistedCubic_ideal_map_eq_standard
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) :
    (Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f))).map
      (linearSubstitution (baseLocusCubicCoefficientMatrix a b c d e)).toRingHom =
        standardTwistedCubicIdeal K := by
  let M := baseLocusCubicCoefficientMatrix a b c d e
  let φ := linearSubstitution M
  let Q := scaledBaseLocusQuadricPolynomials a b c d e f
  have hbe : b * e - c * d ≠ 0 :=
    baseLocus_be_sub_cd_ne_zero_of_delta_zero a b c d e f hb hc hd he hdelta
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (baseLocusCubicCoefficientMatrix_det_ne_zero a b c d e ha hb hc hd he hbe)
  let ψ := linearSubstitutionEquiv M hdet
  have hinj : Function.Injective φ := ψ.injective
  have hind : LinearIndependent K (φ ∘ Q) :=
    (scaledBaseLocusQuadricPolynomials_independent a b c d e f ha hb hc).map_injOn
      φ.toLinearMap hinj.injOn
  have hmem (i : Fin 3) : φ (Q i) ∈ standardTwistedCubicIdeal K := by
    rw [standardTwistedCubicIdeal_eq_ker]
    change ((standardTwistedCubicParam K).comp φ) (Q i) = 0
    rw [← exceptionalTwistedCubicParam_eq_coordinate_change]
    exact exceptionalTwistedCubicParam_scaled_quadric_zero a b c d e f hdelta i
  have h := quadric_ideal_eq_of_independent (φ ∘ Q) (standardTwistedCubicGenerators K)
    (fun i => linearSubstitution_homogeneous M
      (scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f i))
    (standardTwistedCubicGenerators_homogeneous K) hmem hind
  rw [Ideal.map_span, ← Set.range_comp]
  change Ideal.span (Set.range (φ ∘ Q)) = standardTwistedCubicIdeal K
  exact h

theorem exceptionalTwistedCubic_ideal_eq_param_ker
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) :
    Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) =
      RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom := by
  let M := baseLocusCubicCoefficientMatrix a b c d e
  have hbe : b * e - c * d ≠ 0 :=
    baseLocus_be_sub_cd_ne_zero_of_delta_zero a b c d e f hb hc hd he hdelta
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (baseLocusCubicCoefficientMatrix_det_ne_zero a b c d e ha hb hc hd he hbe)
  let ψ := linearSubstitutionEquiv M hdet
  ext P
  rw [← Ideal.apply_mem_of_equiv_iff
    (I := Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)))
    (f := ψ.toRingEquiv)]
  change linearSubstitution M P ∈
    (Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f))).map
      (linearSubstitution M).toRingHom ↔ _
  rw [exceptionalTwistedCubic_ideal_map_eq_standard a b c d e f ha hb hc hd he hdelta,
    standardTwistedCubicIdeal_eq_ker]
  change ((standardTwistedCubicParam K).comp (linearSubstitution M)) P = 0 ↔ _
  rw [← exceptionalTwistedCubicParam_eq_coordinate_change]
  rfl

end QuarticNet
end PfaffianDescent
