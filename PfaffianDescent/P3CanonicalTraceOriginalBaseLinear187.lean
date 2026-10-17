import PfaffianDescent.P3GeneralNegativeTwistTopResidueGroundLinear

/-! Source-only187. Enrich the SAME Laurent-normalized degree-four trace
with linearity for its independently original ambientToBase action. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The prior actual constant-endomorphism identity gives linearity of the
SAME canonical trace, without replacing its original scalar structure. -/
theorem p3NegativeFourCohomologyThreeTraceEquiv_smul187
    [HasExt.{u} (Proj PS).Modules] (c : K) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    ∀ z : schemeModuleCohomology (Proj PS) (sheafOfModules PS 4) 3,
      p3NegativeFourCohomologyThreeTraceEquiv K (c • z) =
        c • p3NegativeFourCohomologyThreeTraceEquiv K z := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  intro z
  rw [Coray.schemeModuleExt_smul_eq_actual_postcomp
    (ambientToBase (R := K) (σ := Fin 4)) z c,
    p3NegativeTwist_scalarEndomorphism_eq_mulHomogeneous K 4 c]
  exact p3NegativeFourCohomologyTrace_scalar_multiplication K c z

/-- Literal original additive canonical trace, with the proved original-base
linearity. It is not an arbitrary functional on a one-dimensional space. -/
def p3NegativeFourCohomologyThreeTraceLinearEquiv187
    [HasExt.{u} (Proj PS).Modules] :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    schemeModuleCohomology (Proj PS) (sheafOfModules PS 4) 3 ≃ₗ[K] K := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  exact
    { toAddEquiv := p3NegativeFourCohomologyThreeTraceEquiv K
      map_smul' := p3NegativeFourCohomologyThreeTraceEquiv_smul187 K }

/-- The canonical additive normalization and every actual trace value are
unchanged. -/
theorem p3NegativeFourCohomologyThreeTraceLinearEquiv_toAddEquiv187
    [HasExt.{u} (Proj PS).Modules] :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    (p3NegativeFourCohomologyThreeTraceLinearEquiv187 K).toAddEquiv =
      p3NegativeFourCohomologyThreeTraceEquiv K := rfl

end PfaffianDescent.ProjectiveNegativeTwist
