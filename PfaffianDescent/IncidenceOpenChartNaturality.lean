import PfaffianDescent.IncidenceOpenChartSubmodule
import PfaffianDescent.CoordinateModuleSheafOver

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable (K : Type u) [CommRing K] (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (U V : (grassmannianScheme K 3 3).Opens)
    (hU : U ≤ (grassmannianChartι K σ).opensRange) (hV : V ≤ U)

lemma grassmannianOpenChartLift_restrict :
    (grassmannianScheme K 3 3).homOfLE hV ≫ grassmannianOpenChartLift K σ U hU =
      grassmannianOpenChartLift K σ V (hV.trans hU) := by
  apply (cancel_mono (grassmannianChartι K σ)).mp
  rw [Category.assoc, grassmannianOpenChartLift_fac, grassmannianOpenChartLift_fac]
  exact Scheme.homOfLE_ι (grassmannianScheme K 3 3) hV

/-- The chosen chart matrix restricts naturally to every smaller open subset. -/
lemma incidenceOpenChartMatrix_restrict :
    (incidenceOpenChartMatrix K σ U hU).map
      (regularFunctionRestrictFrom (grassmannianScheme K 3 3) U V hV) =
      incidenceOpenChartMatrix K σ V (hV.trans hU) := by
  have he := grassmannianOpenChartFunctions_resLE K (𝟙 (grassmannianScheme K 3 3)) U V hV
    (grassmannianOpenChartLift K σ U hU)
  rw [Scheme.Hom.resLE_id, grassmannianOpenChartLift_restrict] at he
  have ha : (Scheme.Hom.appLE (𝟙 (grassmannianScheme K 3 3)) U V hV).hom =
      regularFunctionRestrictFrom (grassmannianScheme K 3 3) U V hV := by
    change (Scheme.Hom.app (𝟙 (grassmannianScheme K 3 3)) U ≫
      (grassmannianScheme K 3 3).presheaf.map (homOfLE hV).op).hom = _
    rw [Scheme.Hom.id_app]
    rfl
  rw [ha] at he
  exact he.symm

end
end PfaffianDescent
