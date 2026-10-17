import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelMatrix

/-! # The actual ground kernel frame internally supplies its projective retraction -/
noncomputable section
namespace PfaffianDescent
open Module
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {W : Type w} [AddCommGroup W] [Module F W]

theorem serreIncidenceGroundKernelMatrix_exists_leftInverse (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bk : Basis (Fin 3) F (LinearMap.ker f)) :
    ∃ N : Matrix (Fin 3) (Fin 9) F,
      N * serreIncidenceGroundKernelMatrix f bV bk = 1 := by
  obtain ⟨n, hn⟩ := (serreIncidenceGroundKernelInclusion f bV bk).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (serreIncidenceGroundKernelInclusion_injective f bV bk))
  refine ⟨LinearMap.toMatrix' n, ?_⟩
  simpa only [serreIncidenceGroundKernelMatrix, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hn

end PfaffianDescent
