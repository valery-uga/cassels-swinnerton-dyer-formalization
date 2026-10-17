import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoordinateStalk
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualBasisRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open SerreExtensionData BundleSectionZeroLocus
universe u

theorem cubicClosedPointSerreFiniteZeroResidual_rankTwoCover_stalk_free
    {X : Scheme.{u}} {N : X.Modules} (e : SerreExtensionData X N)
    (C : SerreExtensionRankTwoAffineCover e) (y : X) :
    letI := schemeModuleStalkModule (show X.Modules from e.E) y
    Module.Free (X.presheaf.stalk y) ((show X.Modules from e.E).presheaf.stalk y) := by
  letI := schemeModuleStalkModule (show X.Modules from e.E) y
  have hx : y ∈ ⨆ k, C.U k := by rw [C.covers]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨k,hk⟩ := hx
  let x : C.U k := ⟨y,hk⟩
  let t := cubicClosedPointSerreFiniteZeroResidual_stalkPairOfFreeIso
    (localFreeIsoOfOver (C.U k) (ULift.{u} (Fin 2)) (C.trivialization k) ≪≫
      (Scheme.Modules.overFunctorEquiv (C.U k)).app e.E) x
  let q : (show X.Modules from e.E).presheaf.stalk y ≃ₗ[X.presheaf.stalk y]
      ((X.presheaf.stalk y) × (X.presheaf.stalk y)) :=
    cubicClosedPointSerreFiniteZeroResidual_restrictionBasis (C.U k) x e.E t
  letI : Module.Free (X.presheaf.stalk y) ((X.presheaf.stalk y) × (X.presheaf.stalk y)) :=
    Module.Free.prod (X.presheaf.stalk y) (X.presheaf.stalk y) (X.presheaf.stalk y)
  exact Module.Free.of_equiv (R := X.presheaf.stalk y) (R' := X.presheaf.stalk y)
    (σ := RingHom.id _) (σ' := RingHom.id _) q.symm
end PfaffianDescent
