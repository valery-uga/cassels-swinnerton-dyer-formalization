import PfaffianDescent.GrassmannianSchemeChartDescentCompatibility
import PfaffianDescent.FiniteLocalizationSubmoduleDescent

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}
  {f : GrassmannianAlgebraPoint K A m n} (d : GrassmannianSchemeFiniteChartData K f)

/-- The actual ambient submodule descended from the graph charts of a scheme point. -/
noncomputable def grassmannianSchemeSubmodule : Submodule A ((Fin m → A) × (Fin n → A)) :=
  finiteLocalizationSubmodule
    (fun a : d.denominators => Localization.Away a.1)
    (fun a : d.denominators => (Fin m → Localization.Away a.1) × (Fin n → Localization.Away a.1))
    (fun a => graphAlgebraCoefficientMap A (Localization.Away a.1) m n)
    (fun a => grassmannianChartSubmodule (Localization.Away a.1) (d.permutation a) (d.matrix a))

/-- The descended submodule restricts to exactly the given chart at every member of the finite cover. -/
theorem grassmannianSchemeSubmodule_baseChange (a : d.denominators) :
    grassmannianSubmoduleBaseChange (algebraMap A (Localization.Away a.1))
      (grassmannianSchemeSubmodule K d) =
        grassmannianChartSubmodule (Localization.Away a.1) (d.permutation a) (d.matrix a) := by
  rw [grassmannianSubmoduleBaseChange_eq_localized A (Localization.Away a.1) m n (.powers a.1)]
  apply finiteLocalizationSubmodule_localized (fun a : d.denominators => a.1)
  intro i j x hx
  rw [graphAlgebraCoefficientMap_apply] at hx
  obtain ⟨e, he⟩ := grassmannianSchemeCharts_clear_denominators K f i.1 j.1
    (d.permutation i) (d.permutation j) (d.matrix i) (d.matrix j) (d.point_eq i) (d.point_eq j) x hx
  refine ⟨e, ?_⟩
  rwa [graphAlgebraCoefficientMap_apply]

end
end PfaffianDescent
