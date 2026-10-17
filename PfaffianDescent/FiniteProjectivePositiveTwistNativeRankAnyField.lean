import PfaffianDescent.FiniteSchemeModuleNativeWeightedRankAnyField
import PfaffianDescent.ProjectivePositiveTwistNativeStalkUnitAnyField
import PfaffianDescent.SchemeModuleSupportedFiberGroundDimension

/-! Source only. Any-field native H0 rank of the ACTUAL finite projective
scheme's positive twist and of its ACTUAL direct image. No global chart,
chosen sheaf trivialization, quotient-Iso or desired rank premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial AllCharacteristics
open AllCharacteristics.HomogeneousProjective
open PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {K : Type u} {σ : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- For the SAME finite structural morphism and native positive coefficient,
global section rank is the entire finite scheme rank over any original field.
The weighted local lengths and finiteness are derived internally. -/
theorem finiteProjectivePositiveTwist_topSections_finite_and_nativeRank_anyField
    (I : HomogeneousIdeal (homogeneousSubmodule σ K)) (m : ℕ)
    (g : scheme I ⟶ Spec (.of K)) [IsFinite g] :
    Module.Finite K (SchemeModuleOpenSectionsOver g
      (positiveSheafOfModules (grading I) m) ⊤) ∧
    Module.finrank K (SchemeModuleOpenSectionsOver g
      (positiveSheafOfModules (grading I) m) ⊤) = finiteSchemeRank g :=
  finiteSchemeModuleTopSections_finite_and_nativeRank_of_stalkLength_anyField
    g (positiveSheafOfModules (grading I) m)
    (quotientPositiveTwist_nativeStalk_length_anyField I m)

/-- The ACTUAL pushed-forward positive coefficient has the same native rank
under the independent original ambient pi action. The existing canonical
pushforward section equivalence proves the scalar compatibility. -/
theorem finiteProjectivePushforwardPositiveTwist_topSections_finite_and_nativeRank_anyField
    (I : HomogeneousIdeal (homogeneousSubmodule σ K)) (m : ℕ)
    {Y : Scheme.{u}} (pi : Y ⟶ Spec (.of K)) (i : scheme I ⟶ Y)
    [IsFinite (i ≫ pi)] :
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pushforward i).obj (positiveSheafOfModules (grading I) m)) ⊤) ∧
    Module.finrank K (SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pushforward i).obj (positiveSheafOfModules (grading I) m)) ⊤) =
        finiteSchemeRank (i ≫ pi) := by
  have h := finiteProjectivePositiveTwist_topSections_finite_and_nativeRank_anyField
    I m (i ≫ pi)
  letI := h.1
  let e := schemeModulePushforward_topSectionsLinearEquiv pi i
    (positiveSheafOfModules (grading I) m)
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h.2⟩

end PfaffianDescent.Coray
