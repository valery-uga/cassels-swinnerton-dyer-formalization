import PfaffianDescent.GrassmannianOpenChartFunctions
import PfaffianDescent.IncidenceSheafMatrixSections

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (U : (grassmannianScheme K 3 3).Opens) (hU : U ≤ (grassmannianChartι K σ).opensRange)
include hU

/-- The actual chart factorization of an open subset contained in a Grassmannian chart. -/
noncomputable def grassmannianOpenChartLift : U.toScheme ⟶ grassmannianChartScheme K 3 3 :=
  IsOpenImmersion.lift (grassmannianChartι K σ) U.ι (by
    rw [Scheme.Opens.range_ι]
    exact hU)

lemma grassmannianOpenChartLift_fac :
    grassmannianOpenChartLift K σ U hU ≫ grassmannianChartι K σ = U.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- Tautological graph coordinates in the original open section ring. -/
noncomputable def incidenceOpenChartMatrix : Matrix (Fin 3) (Fin 3) Γ(grassmannianScheme K 3 3, U) :=
  grassmannianOpenChartFunctions K U (grassmannianOpenChartLift K σ U hU)

/-- Restricting the chosen chart to any other chart gives the same actual tautological submodule. -/
lemma incidenceOpenChartSubmodule (τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    grassmannianChartSubmodule Γ(grassmannianChartScheme K 3 3, (grassmannianChartι K τ) ⁻¹ᵁ U) σ
      ((incidenceOpenChartMatrix K σ U hU).map ((grassmannianChartι K τ).app U).hom) =
      grassmannianChartSubmodule Γ(grassmannianChartScheme K 3 3, (grassmannianChartι K τ) ⁻¹ᵁ U) τ
        (incidenceChartRestrictedMatrix K U τ) := by
  let j := grassmannianChartι K τ
  let V := j ⁻¹ᵁ U
  let q := grassmannianOpenChartLift K σ U hU
  have hc : (j.resLE U V le_rfl ≫ q) ≫ grassmannianChartι K σ = V.ι ≫ grassmannianChartι K τ := by
    rw [Category.assoc, grassmannianOpenChartLift_fac]
    exact Scheme.Hom.resLE_comp_ι j le_rfl
  have hw := grassmannianOpenChartFunctions_submodule_eq K V σ τ
    (j.resLE U V le_rfl ≫ q) V.ι hc
  have ha := grassmannianOpenChartFunctions_resLE K j U V le_rfl q
  have hb : grassmannianOpenChartFunctions K V V.ι = incidenceChartRestrictedMatrix K U τ :=
    (congrArg (grassmannianOpenChartFunctions K V) (Category.comp_id V.ι).symm).trans
      (grassmannianOpenChartFunctions_restrict K V (𝟙 (grassmannianChartScheme K 3 3)))
  rw [ha, hb] at hw
  have happ : j.appLE U V le_rfl = j.app U := Scheme.Hom.appLE_eq_app j
  rw [happ] at hw
  exact hw

end
end PfaffianDescent
