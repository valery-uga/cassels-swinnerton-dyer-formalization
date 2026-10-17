import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
section
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K)) [IsSeparated f]

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedCanonicalEndpoint_finite
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    [IsFinite (C.localPencilZeroGluedToAmbient e seed (𝟙 _) 0 ≫ f)] :
    ((C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed ≫
      projectiveLineAmbientToLine K f) ⁻¹'
        {projectiveLineEndpoint K false (IsLocalRing.closedPoint K)}).Finite := by
  let i := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  let ep := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f false
  let g := i ≫ projectiveLineAmbientToLine K f
  let c := C.localPencilZeroGluedToAmbient e seed (𝟙 _) 0 ≫ f
  have hC : (Set.univ : Set (C.localPencilZeroGluedScheme e seed (𝟙 _) 0)).Finite := by
    simpa using c.finite_preimage (Set.finite_univ (α := Spec (.of K)))
  letI : Finite (C.localPencilZeroGluedScheme e seed (𝟙 _) 0) := Set.finite_univ_iff.mp hC
  let a := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpoint_iso f C seed
  letI : Finite ↥(pullback i ep) := Finite.of_injective
    (fun x : ↥(pullback i ep) => a.hom x) a.hom.injective
  have h : IsPullback (pullback.fst i ep) (pullback.snd i ep ≫ f) g
      (projectiveLineEndpoint K false) :=
    (IsPullback.of_hasPullback i ep).paste_vert
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_isPullback f false)
  letI : Finite ↥(pullback g (projectiveLineEndpoint K false)) :=
    Finite.of_injective (fun x : ↥(pullback g (projectiveLineEndpoint K false)) =>
      h.isoPullback.inv x) h.isoPullback.inv.injective
  have hf := Set.finite_range (pullback.fst g (projectiveLineEndpoint K false))
  rw [Scheme.Pullback.range_fst] at hf
  have hr : Set.range (projectiveLineEndpoint K false) =
      {projectiveLineEndpoint K false (IsLocalRing.closedPoint K)} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_singleton_iff.mpr
        (congrArg (projectiveLineEndpoint K false) (Subsingleton.elim z (IsLocalRing.closedPoint K)))
    · intro hy
      exact ⟨IsLocalRing.closedPoint K, (Set.mem_singleton_iff.mp hy).symm⟩
  rw [hr] at hf
  exact hf

end
end PfaffianDescent
