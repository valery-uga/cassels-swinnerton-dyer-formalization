import AllCharacteristics.ManuscriptVerification.Audit
import AllCharacteristics.InternalCorayPaperConclusions

set_option pp.universes true
set_option pp.deepTerms true

#check @AllCharacteristics.internalCorayDegreeOneFourOrTenFor_uniform001
#print axioms AllCharacteristics.internalCorayDegreeOneFourOrTenFor_uniform001

open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  liftIO <| ManuscriptVerification.inspect env #[`AllCharacteristics.internalCorayDegreeOneFourOrTenFor_uniform001] (forbidden := #[
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
