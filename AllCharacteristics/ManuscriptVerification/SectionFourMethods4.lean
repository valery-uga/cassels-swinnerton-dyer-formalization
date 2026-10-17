import AllCharacteristics.ManuscriptVerification.Audit
import PfaffianDescent.FourCoordinateVertexActualH0LiteralWhole
import PfaffianDescent.QuarticExceptionalNativeCubicHZeroBasis

set_option pp.universes true
set_option pp.deepTerms true

#check @PfaffianDescent.fourCoordinateVertex_whole_actual_choice_independent_H0_literal_presentation
#print axioms PfaffianDescent.fourCoordinateVertex_whole_actual_choice_independent_H0_literal_presentation
#check @PfaffianDescent.QuarticNet.baseLocusExceptionalNativeHZero_completeBasis
#print axioms PfaffianDescent.QuarticNet.baseLocusExceptionalNativeHZero_completeBasis

open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  liftIO <| ManuscriptVerification.inspect env #[`PfaffianDescent.fourCoordinateVertex_whole_actual_choice_independent_H0_literal_presentation,
  `PfaffianDescent.QuarticNet.baseLocusExceptionalNativeHZero_completeBasis] (allowDefinitions := true) (forbidden := #[
  `AllCharacteristics.twoProofs_degree_five_has_point,
  `AllCharacteristics.twoProofs_pfaffian_cubic_has_point,
  `AllCharacteristics.twoProofs_incidence_finite_etale_degree_two_open,
  `AllCharacteristics.twoProofs_reduced_length_five_subscheme_pfaffian,
  `AllCharacteristics.twoProofs_non_coplanar_quintic_has_point,
  `AllCharacteristics.twoProofs_non_coplanar_quintic_has_point_of_not_ground_plane,
  `PfaffianDescent.projective_pfaffian_to_point,
  `PfaffianDescent.reduced_length_five_subscheme_pfaffian,
  `PfaffianDescent.incidence_finite_etale_degree_two_open,
  `PfaffianDescent.quintic_geometric_pfaffian_presentation,
  `PfaffianDescent.pfaffian_to_point,
  `PfaffianDescent.cubic_degree_five_descent,
  `PfaffianDescent.cubic_descent_of_quintic_surjective,
  `PfaffianDescent.cubic_descent_of_independent_quintic_point,
  `PfaffianDescent.canonical_quintic_tensor_descent,
  `PfaffianDescent.projective_cubic_degree_five_descent,
  `PfaffianDescent.projective_cubic_effective_degree_five_to_point])
