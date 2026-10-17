import AllCharacteristics.ManuscriptVerification.Audit
open Lean Elab Command
theorem publicationValid : True := True.intro
run_cmd do
  let env ← getEnv
  liftIO (ManuscriptVerification.inspect (env.setExporting false) #[`publicationValid])
