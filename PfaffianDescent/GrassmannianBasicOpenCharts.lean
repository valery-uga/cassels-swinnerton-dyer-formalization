import PfaffianDescent.GrassmannianCoordinateBaseChange
import PfaffianDescent.LinearMapLocalizationOpen

namespace PfaffianDescent
open Module
section
variable (R : Type*) [CommRing R] {m n : ℕ}

/-- Every finite projective quotient has a standard graph chart on a basic neighborhood of each prime. -/
theorem grassmannian_quotient_exists_basic_chart
    (W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n) (p : PrimeSpectrum R) :
    ∃ a : R, a ∉ p.asIdeal ∧ ∃ (σ : Equiv.Perm (Fin m ⊕ Fin n))
      (T : Matrix (Fin n) (Fin m) (Localization.Away a)),
      grassmannianSubmoduleBaseChange (algebraMap R (Localization.Away a)) W.toSubmodule =
        grassmannianChartSubmodule (Localization.Away a) σ T := by
  let Rp := Localization.AtPrime p.asIdeal
  obtain ⟨σ, hσ⟩ := grassmannian_local_quotient_coordinates Rp (grassmannianQuotientBaseChange R Rp W)
  have hp : Function.Bijective ((grassmannianQuotientCoordinateMap R W.toSubmodule σ).baseChange Rp) :=
    grassmannianQuotientCoordinateMap_baseChange_bijective R Rp W.toSubmodule σ hσ
  haveI : Module.FinitePresentation R (((Fin m → R) × (Fin n → R)) ⧸ W.toSubmodule) :=
    Module.finitePresentation_of_projective R _
  obtain ⟨a, ha, hfa⟩ := linearMap_exists_away_bijective (grassmannianQuotientCoordinateMap R W.toSubmodule σ) p hp
  have hb := (grassmannianQuotientCoordinateMap_baseChange_bijective_iff R (Localization.Away a) W.toSubmodule σ).mp hfa
  obtain ⟨T, hT⟩ := (grassmannianQuotientCoordinateMap_iff_graph (Localization.Away a)
    (grassmannianSubmoduleBaseChange (algebraMap R (Localization.Away a)) W.toSubmodule) σ).mp hb
  exact ⟨a, ha, σ, T, hT⟩

end
end PfaffianDescent
