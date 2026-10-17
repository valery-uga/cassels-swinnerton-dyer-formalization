import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelColumns

/-! # Literal coordinates of an actual kernel basis span the native matrix kernel -/
noncomputable section
namespace PfaffianDescent
open Module
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {E : Type u} [Field E]
variable {V : Type v} [AddCommGroup V] [Module E V]
variable {W : Type w} [AddCommGroup W] [Module E W]

theorem serreIncidenceNativeKernelColumns_range
    (f : V →ₗ[E] W) (bV : Basis (Fin 9) E V)
    (coord : W ≃ₗ[E] (Fin 6 → E)) (bk : Basis (Fin 3) E (LinearMap.ker f))
    (A : Matrix (Fin 6) (Fin 9) E) (M : Matrix (Fin 9) (Fin 3) E)
    (hA : ∀ v, Matrix.toLin' A (bV.equivFun v) = coord (f v))
    (hM : ∀ i k, M i k = bV.equivFun (bk k : V) i) :
    LinearMap.range (Matrix.toLin' M) = LinearMap.ker (Matrix.toLin' A) := by
  have hi : (Matrix.toLin' M).comp bk.equivFun.toLinearMap =
      bV.equivFun.toLinearMap.comp (LinearMap.ker f).subtype := by
    apply bk.ext
    intro k
    have hk : bk.equivFun (bk k) = Pi.single k 1 := by
      ext i
      rw [Basis.equivFun_self]
      simp only [Pi.single_apply, eq_comm]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hk, Matrix.toLin'_apply]
    simp only [Matrix.mulVec_single]
    change (1 : Eᵐᵒᵖ) • M.col k = bV.equivFun (bk k : V)
    rw [one_smul]
    ext i
    exact hM i k
  have his : ∀ s : LinearMap.ker f,
      Matrix.toLin' M (bk.equivFun s) = bV.equivFun (s : V) :=
    fun s => LinearMap.congr_fun hi s
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    have hv := his (bk.equivFun.symm v)
    rw [bk.equivFun.apply_symm_apply] at hv
    change Matrix.toLin' A (Matrix.toLin' M v) = 0
    rw [hv, hA]
    have hz : f ((bk.equivFun.symm v : LinearMap.ker f) : V) = 0 :=
      (bk.equivFun.symm v).property
    rw [hz, map_zero]
  · intro hx
    have hz : f (bV.equivFun.symm x) = 0 := by
      apply coord.injective
      rw [map_zero, ← hA, bV.equivFun.apply_symm_apply]
      exact hx
    let s : LinearMap.ker f := ⟨bV.equivFun.symm x, hz⟩
    refine ⟨bk.equivFun s, ?_⟩
    rw [his]
    exact bV.equivFun.apply_symm_apply x

end PfaffianDescent
