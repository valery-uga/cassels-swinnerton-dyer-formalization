import AllCharacteristics.Corollary13Unirationality
import AllCharacteristics.ManuscriptVerification.Audit

/-!
# Audit of the unconditional unirationality corollary

Inspect the actual exported types and transitive proof dependencies of the
arbitrary-field point-to-unirationality theorem and Corollary 1.3. The audit
requires the constructed generic secant preimage, the smooth-cubic no-line
argument, characteristic-two residual separability, explicit coefficient
base change, and the actual affine source. The zero-cycle equivalence also
requires the internally proved Cassels–Swinnerton-Dyer theorem.

`ManuscriptVerification.inspect` rejects every axiom outside `propext`,
`Classical.choice`, and `Quot.sound`, including `sorryAx`. This inspects the
imported checked environment; it is not fresh Comparator kernel replay.
-/

set_option pp.deepTerms true in
#check @AllCharacteristics.isUnirationalOver_normalized_smooth_cubic
#print axioms AllCharacteristics.isUnirationalOver_normalized_smooth_cubic

set_option pp.deepTerms true in
#check @AllCharacteristics.smoothCubic_unirational_of_rational_section
#print axioms AllCharacteristics.smoothCubic_unirational_of_rational_section

set_option pp.deepTerms true in
#check @AllCharacteristics.twoProofs_corollary13_unirational_iff_zeroCycle_degree_one
#print axioms AllCharacteristics.twoProofs_corollary13_unirational_iff_zeroCycle_degree_one

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name :=
    #[`sorryAx,
      `AllCharacteristics.HomogeneousProjective.SmoothCubicPointUnirationalFor,
      `AllCharacteristics.HomogeneousProjective.twoProofs_unirational_iff_zeroCycle_degree_one,
      `AllCharacteristics.HomogeneousProjective.twoProofs_unirational_iff_zeroCycle_degree_one_of_infinite]
  let constructedGeometry : Array Name :=
    #[`AllCharacteristics.isUnirationalOver_normalized_smooth_cubic,
      `AllCharacteristics.nonempty_kollarNormalizedCubic_of_section,
      `AllCharacteristics.exists_kollar_coordinate_normalization,
      `AllCharacteristics.kollarNormalized_raw_secant_nonzero_and_detects,
      `AllCharacteristics.universal_secant_generic_witness_of_geometric_centers,
      `AllCharacteristics.exists_two_tangent_secant_preimage_of_smooth_generic_target,
      `AllCharacteristics.smoothCubic_generic_no_contained_line_through,
      `AllCharacteristics.kollar_residual_center_linearIndependent,
      `AllCharacteristics.kollarResidualRootBaseChange,
      `AllCharacteristics.kollarGenericResidualPolynomial_separable_of_smooth,
      `AllCharacteristics.kollar_generic_projective_line_residual_separable_charTwo,
      `AllCharacteristics.HomogeneousProjective.exists_dominant_projective_point_of_homogeneous_relations,
      `AllCharacteristics.kollarUniversalSourceAffineIso,
      `AllCharacteristics.kollarUniversalSourceAffineIso_over,
      `AllCharacteristics.HomogeneousProjective.isUnirationalOver_of_affineIso_genericFieldPoint]
  liftIO <| ManuscriptVerification.inspect (env.setExporting false)
    #[`AllCharacteristics.smoothCubic_unirational_of_rational_section]
    forbidden constructedGeometry
  liftIO <| ManuscriptVerification.inspect (env.setExporting false)
    #[`AllCharacteristics.twoProofs_corollary13_unirational_iff_zeroCycle_degree_one]
    forbidden
    (constructedGeometry ++
      #[`AllCharacteristics.twoProofs_main_theorem_internalCoray001,
        `AllCharacteristics.HomogeneousProjective.zeroCycle_degree_one_of_unirational_smoothCubic])
