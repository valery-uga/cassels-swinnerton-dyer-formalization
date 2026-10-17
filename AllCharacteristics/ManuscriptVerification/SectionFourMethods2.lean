import AllCharacteristics.ManuscriptVerification.Audit
import PfaffianDescent.ActualP3IdealQuadraticGlobalBaseFieldExtension

set_option pp.universes true
set_option pp.deepTerms true

#check @PfaffianDescent.p3ActualIdealQuadraticGlobalBaseIdeal_actual_fieldExtension
#print axioms PfaffianDescent.p3ActualIdealQuadraticGlobalBaseIdeal_actual_fieldExtension
#check @PfaffianDescent.p3ActualIdealQuadraticHZero_actual_fieldExtension_finrank
#print axioms PfaffianDescent.p3ActualIdealQuadraticHZero_actual_fieldExtension_finrank

open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  liftIO <| ManuscriptVerification.inspect env #[`PfaffianDescent.p3ActualIdealQuadraticGlobalBaseIdeal_actual_fieldExtension,
  `PfaffianDescent.p3ActualIdealQuadraticHZero_actual_fieldExtension_finrank] (allowDefinitions := true) (forbidden := #[
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
