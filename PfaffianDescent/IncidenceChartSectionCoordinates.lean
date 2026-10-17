import PfaffianDescent.RelativeAffineFunctions
import PfaffianDescent.CategoricalSectionsEquiv
import PfaffianDescent.IncidenceLocalTrivialization

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}}
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (g : X ⟶ grassmannianChartScheme K 3 3)

/-- On every test scheme over a Grassmannian chart, the actual incidence space represents thirty-six regular functions. -/
noncomputable def incidenceChartSectionCoordinates :
    {f : X ⟶ incidenceScheme K // f ≫ incidenceToGrassmannian K = g ≫ grassmannianChartι K σ} ≃
      (IncidenceFiberIndex → Γ(X, ⊤)) :=
  (pullbackSectionsEquiv (incidenceGrassmannianChart_isPullback K σ) g).trans
    ((isoSectionsEquiv (incidenceChartProductIso K) (incidenceGraphToGrassmannianChart K)
      (relativeAffineProjection (GrassmannianChartRing K 3 3) IncidenceFiberIndex)
      (incidenceChartProductIso_toGrassmannian K) g).trans
      (relativeAffineFunctionsEquiv (GrassmannianChartRing K 3 3) IncidenceFiberIndex g))

end
end PfaffianDescent
