import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelSplit

/-! # Literal ground section coordinates for an actual restriction-kernel basis -/
noncomputable section
namespace PfaffianDescent
open Module
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {W : Type w} [AddCommGroup W] [Module F W]

def serreIncidenceGroundKernelInclusion (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bk : Basis (Fin 3) F (LinearMap.ker f)) :
    (Fin 3 → F) →ₗ[F] (Fin 9 → F) :=
  bV.equivFun.toLinearMap.comp
    ((LinearMap.ker f).subtype.comp bk.equivFun.symm.toLinearMap)

def serreIncidenceGroundEvaluationCoordinates (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bW : Basis (Fin 6) F W) :
    (Fin 9 → F) →ₗ[F] (Fin 6 → F) :=
  bW.equivFun.toLinearMap.comp (f.comp bV.equivFun.symm.toLinearMap)

theorem serreIncidenceGroundKernelInclusion_injective (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bk : Basis (Fin 3) F (LinearMap.ker f)) :
    Function.Injective (serreIncidenceGroundKernelInclusion f bV bk) := by
  exact bV.equivFun.injective.comp (Subtype.val_injective.comp bk.equivFun.symm.injective)

theorem serreIncidenceGroundKernelInclusion_range (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bW : Basis (Fin 6) F W)
    (bk : Basis (Fin 3) F (LinearMap.ker f)) :
    LinearMap.range (serreIncidenceGroundKernelInclusion f bV bk) =
      LinearMap.ker (serreIncidenceGroundEvaluationCoordinates f bV bW) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change bW.equivFun (f (bV.equivFun.symm
      (bV.equivFun ((bk.equivFun.symm t : LinearMap.ker f) : V)))) = 0
    rw [LinearEquiv.symm_apply_apply]
    have hmem : f ((bk.equivFun.symm t : LinearMap.ker f) : V) = 0 :=
      (bk.equivFun.symm t).property
    rw [hmem, map_zero]
  · intro hx
    have hx' : f (bV.equivFun.symm x) = 0 := by
      apply bW.equivFun.injective
      change bW.equivFun (f (bV.equivFun.symm x)) = 0 at hx
      simpa only [map_zero] using hx
    refine ⟨bk.equivFun ⟨bV.equivFun.symm x, hx'⟩, ?_⟩
    change bV.equivFun ((bk.equivFun.symm
      (bk.equivFun ⟨bV.equivFun.symm x, hx'⟩) : LinearMap.ker f) : V) = x
    rw [LinearEquiv.symm_apply_apply]
    exact bV.equivFun.apply_symm_apply x

end PfaffianDescent
