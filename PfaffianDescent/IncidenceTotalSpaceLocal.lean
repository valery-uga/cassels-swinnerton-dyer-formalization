import PfaffianDescent.IncidenceChartSectionCoordinates
import PfaffianDescent.IncidenceKernelSheafLocalFree

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

/-- Actual scheme sections of the incidence projection over an open subset of the Grassmannian. -/
def IncidenceSchemeSections (U : (grassmannianScheme K 3 3).Opens) :=
  {f : U.toScheme ⟶ incidenceScheme K // f ≫ incidenceToGrassmannian K = U.ι}

noncomputable def incidenceSchemeSectionsRestrict
    (U V : (grassmannianScheme K 3 3).Opens) (h : V ≤ U)
    (s : IncidenceSchemeSections K U) : IncidenceSchemeSections K V :=
  ⟨(grassmannianScheme K 3 3).homOfLE h ≫ s.1, by
    rw [Category.assoc, s.2]
    exact Scheme.homOfLE_ι _ h⟩

/-- On a chart, actual scheme sections have the same thirty-six regular coordinates as the kernel sheaf. -/
noncomputable def incidenceSchemeSectionFunctions
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (U : (grassmannianScheme K 3 3).Opens)
    (hU : U ≤ (grassmannianChartι K σ).opensRange) :
    IncidenceSchemeSections K U ≃ (IncidenceFiberIndex → Γ(grassmannianScheme K 3 3, U)) := by
  let e : IncidenceSchemeSections K U ≃
      {f : U.toScheme ⟶ incidenceScheme K // f ≫ incidenceToGrassmannian K =
        grassmannianOpenChartLift K σ U hU ≫ grassmannianChartι K σ} :=
    Equiv.subtypeEquivRight (fun f => by rw [grassmannianOpenChartLift_fac])
  exact e.trans ((incidenceChartSectionCoordinates K σ (grassmannianOpenChartLift K σ U hU)).trans
    (Equiv.piCongrRight (fun _ : IncidenceFiberIndex => U.topIso.commRingCatIsoToRingEquiv.toEquiv)))

/-- On each chart, the actual incidence scheme represents sections of the actual rank-thirty-six kernel sheaf. -/
noncomputable def incidenceSchemeKernelSectionsOnChart
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (U : (grassmannianScheme K 3 3).Opens)
    (hU : U ≤ (grassmannianChartι K σ).opensRange) :
    IncidenceSchemeSections K U ≃ Γ(incidenceKernelSheaf K, U) :=
  (incidenceSchemeSectionFunctions K σ U hU).trans
    (incidenceKernelSheafOpenSectionsEquiv K σ U hU).symm.toEquiv

end
end PfaffianDescent
