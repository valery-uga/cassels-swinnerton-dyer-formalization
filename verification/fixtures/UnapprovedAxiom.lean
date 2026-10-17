import AllCharacteristics.ManuscriptVerification.Audit
open Lean Elab Command
axiom publicationUnapproved : False
theorem publicationBad : False := publicationUnapproved
run_cmd do
  let env ← getEnv
  liftIO (ManuscriptVerification.inspect (env.setExporting false) #[`publicationBad])
