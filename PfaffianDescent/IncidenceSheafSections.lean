import PfaffianDescent.IncidenceKernelSheaf
import PfaffianDescent.SheafProductSections

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
section
variable (K : Type u) [CommRing K] (U : (grassmannianScheme K 3 3).Opens)

/-- Ambient regular coefficient tuples satisfying every chart restriction equation. -/
noncomputable def incidenceEquationSections :
    Submodule Γ(grassmannianScheme K 3 3, U) (AlternatingTripleIndex → Γ(grassmannianScheme K 3 3, U)) :=
  simultaneousSheafKernel (grassmannianScheme K 3 3).ringCatSheaf
    (fun σ => incidenceChartEquationSheaf K σ) (op U) (incidenceChartRestrictionSheafMap K)

lemma mem_incidenceEquationSections (c : AlternatingTripleIndex → Γ(grassmannianScheme K 3 3, U)) :
    c ∈ incidenceEquationSections K U ↔
      ∀ σ, (incidenceChartRestrictionSheafMap K σ).val.app (op U) c = 0 :=
  mem_simultaneousSheafKernel (grassmannianScheme K 3 3).ringCatSheaf
    (fun σ => incidenceChartEquationSheaf K σ) (op U) (incidenceChartRestrictionSheafMap K) c

lemma incidenceRestrictionSheafMap_kernel_sections :
    ((incidenceRestrictionSheafMap K).val.app (op U)).hom.ker = incidenceEquationSections K U :=
  sheafProductSections_kernel (grassmannianScheme K 3 3).ringCatSheaf
    (fun σ => incidenceChartEquationSheaf K σ) (op U) (incidenceChartRestrictionSheafMap K)

/-- Sections of the actual incidence kernel sheaf are exactly the simultaneous concrete isotropy equations. -/
noncomputable def incidenceKernelSheafSectionsEquiv :
    Γ(incidenceKernelSheaf K, U) ≃ₗ[Γ(grassmannianScheme K 3 3, U)] incidenceEquationSections K U :=
  sheafSimultaneousKernelSectionsEquiv (grassmannianScheme K 3 3).ringCatSheaf
    (fun σ => incidenceChartEquationSheaf K σ) (op U) (incidenceChartRestrictionSheafMap K)

lemma incidenceKernelSheafSectionsEquiv_val (x : Γ(incidenceKernelSheaf K, U)) :
    (incidenceKernelSheafSectionsEquiv K U x).1 = (incidenceKernelSheafι K).val.app (op U) x :=
  sheafSimultaneousKernelSectionsEquiv_val (grassmannianScheme K 3 3).ringCatSheaf
    (fun σ => incidenceChartEquationSheaf K σ) (op U) (incidenceChartRestrictionSheafMap K) x

end
end PfaffianDescent
