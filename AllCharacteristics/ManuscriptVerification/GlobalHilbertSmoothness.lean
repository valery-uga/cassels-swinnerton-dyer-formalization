import PfaffianDescent.OriginalLiftedCubicGlobalHilbertSmooth
import AllCharacteristics.ManuscriptVerification.Audit

/-! Global smoothness of the actual representing Hilbert scheme.
The audit requires the arbitrary-family construction in the proof closure
and excludes the earlier closed-point-only smooth-classifier theorem.
This is an imported-environment audit, not a Comparator kernel replay. -/

set_option pp.deepTerms true in
#check @PfaffianDescent.originalLiftedCubicGlobalHilbert_smooth_flat001
#print axioms PfaffianDescent.originalLiftedCubicGlobalHilbert_smooth_flat001

set_option pp.deepTerms true in
#check @PfaffianDescent.originalNormalizedPolynomialGlobalHilbert_smooth_flat_primitive_smooth_cubic001
#print axioms PfaffianDescent.originalNormalizedPolynomialGlobalHilbert_smooth_flat_primitive_smooth_cubic001

set_option pp.deepTerms true in
#check @PfaffianDescent.originalCubic_physicalArtinianSquareZeroLifts001
#print axioms PfaffianDescent.originalCubic_physicalArtinianSquareZeroLifts001

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| ManuscriptVerification.inspect (env.setExporting false)
    #[`PfaffianDescent.originalLiftedCubicGlobalHilbert_smooth_flat001,
      `PfaffianDescent.originalNormalizedPolynomialGlobalHilbert_smooth_flat_primitive_smooth_cubic001,
      `PfaffianDescent.originalCubic_physicalArtinianSquareZeroLifts001]
    #[`PfaffianDescent.originalClosedPoint_globalHilbertSmoothClassifierLift_completeAlgebra001,
      `PfaffianDescent.originalCoefficientTestGlobalClassifyingMap_mem_smoothLocus001]
    #[`PfaffianDescent.exists_arbitraryCubicArtinFamily_physicalLift001,
      `PfaffianDescent.exists_originalArtinSupport_principal_hilbertBurch318,
      `AllCharacteristics.exists_actual_artin_semilocal_hilbertBurch_resolution318]
