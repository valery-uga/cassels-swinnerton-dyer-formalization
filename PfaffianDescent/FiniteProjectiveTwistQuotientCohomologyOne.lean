import PfaffianDescent.FiniteProjectiveTwistQuotientRank
import PfaffianDescent.FiniteSchemeUnitCohomologyOne

/-! SOURCE ONLY168. Every-degree H1 vanishing of the LITERAL entire finite
projective twisted ideal quotient.158's actual coefficient iso and162's
finite-unit acyclicity supply this; no supplied acyclicity, quotient model,
Riemann--Roch, or section-bound premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual twisted ideal-sequence quotient has zero intrinsic H1 for
EVERY d. The entire finite subscheme is retained, including nilpotents. -/
theorem finiteProjectivePositiveTwistQuotient_cohomology_one_subsingleton168
    {σ : Type} [Finite σ] [Infinite K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (d : ℕ)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    [HasExt.{u} (scheme I).Modules] :
    Subsingleton (schemeModuleCohomology (scheme I)
      (PfaffianDescent.closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading I) d)).X₃ 1) := by
  letI : Subsingleton (schemeModuleCohomology (scheme I)
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) 1) :=
    finiteClosedImmersionUnitPushforward_cohomology_one_subsingleton (toBase I) i
  exact schemeModuleCohomology_subsingleton_of_iso (scheme I)
    (PfaffianDescent.finiteProjectiveClosedSubschemePositiveTwistProjectionFormulaIso
      I d i).symm 1

end PfaffianDescent.Coray
