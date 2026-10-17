import AllCharacteristics.ManuscriptVerification.Audit
open Lean Elab Command
theorem publicationSorry : False := by sorry
run_cmd do
  let env ← getEnv
  liftIO (ManuscriptVerification.inspect (env.setExporting false) #[`publicationSorry])
