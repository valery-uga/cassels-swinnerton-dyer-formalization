import PfaffianDescent.IncidenceEmbedding
import PfaffianDescent.GrassmannianProper

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] [IsNoetherianRing K]

/-- The global common-isotropic incidence projection is proper. -/
instance incidenceToTriples_isProper : IsProper (incidenceToTriples K) := by
  rw [← incidenceEmbedding_snd]
  haveI : IsProper (incidenceEmbedding K) := inferInstance
  haveI : IsProper (pullback.snd (grassmannianToBase K 3 3) (alternatingTripleToBase K)) := inferInstance
  infer_instance

end
end PfaffianDescent
