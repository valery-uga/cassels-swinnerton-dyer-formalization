import PfaffianDescent.VoisinCartierInverseTwist
import PfaffianDescent.SchemeModuleLocallyRankOneTensor

/-! Actual rank-one neighborhoods for the SAME regular-principal ideal.
SOURCE ONLY / UNVERIFIED. No numerical or cohomology premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- Regular-principal equations give actual UNIT neighborhoods, not merely
an unspecified finite locally free rank, for the literal immersion ideal. -/
theorem RegularPrincipalImmersion.inverseCartierTwist_locallyRankOne
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) :
    schemeModuleLocallyRankOne H.inverseCartierTwist := by
  classical
  intro x
  obtain ⟨j, y, hy⟩ := H.cover x
  letI : IsOpenImmersion (H.target j) := H.targetOpen j
  let W : (Spec (H.A j)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
  let U : X.affineOpens :=
    ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  have hxU : x ∈ U.1 := by
    change x ∈ H.target j ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩
  let chartMap := H.chartIdealModuleHom j
  let e₀ : SheafOfModules.unit (U.1 : Scheme.{u}).ringCatSheaf ≅
      H.inverseCartierTwist.restrict U.1.ι :=
    @asIso _ _ _ _ chartMap (H.chartIdealModuleHom_isIso j)
  exact ⟨U.1, hxU,
    ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e₀.symm⟩⟩

end PfaffianDescent
