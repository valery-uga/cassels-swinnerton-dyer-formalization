import PfaffianDescent.QuadraticSkewConjugateProjectorFrame
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! SOURCE ONLY / UNCOMPILED. Projection and paired frame from ordinary
rank-two vector subspaces representing two skew linear lines. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.OrdinaryLines201
open Module QuarticNet PairedFrame
universe u
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- Rank two and zero vector intersection imply a complementary decomposition. -/
theorem rankTwoSkew_isCompl201
    (U V : Submodule E (Fin 4 → E))
    (hU : finrank E U = 2) (hV : finrank E V = 2)
    (hSkew : Disjoint U V) : IsCompl U V := by
  apply (Submodule.isCompl_iff_disjoint U V ?_).mpr hSkew
  simpa only [Module.finrank_pi, Fintype.card_fin, hU, hV] using (Nat.le_refl 4)

def skewLineProjector201
    (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V) :
    Matrix (Fin 4) (Fin 4) E :=
  LinearMap.toMatrix' (U.projection V h)

theorem skewLineProjector_mulVec201
    (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V) (x : Fin 4 → E) :
    (skewLineProjector201 U V h).mulVec x = U.projection V h x := by
  exact LinearMap.toMatrix'_mulVec _ x

theorem skewLineProjector_mulVecLin201
    (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V) :
    (skewLineProjector201 U V h).mulVecLin = U.projection V h := by
  apply LinearMap.ext
  intro x
  exact skewLineProjector_mulVec201 U V h x

theorem skewLineProjector_complement_mulVecLin201
    (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V) :
    (1 - skewLineProjector201 U V h).mulVecLin = V.projection U h.symm := by
  apply LinearMap.ext
  intro x
  change (1 - skewLineProjector201 U V h).mulVec x = _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, skewLineProjector_mulVec201]
  exact (Submodule.projection_eq_self_sub_projection h x).symm

theorem skewLineProjector_complement201
    (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V) :
    skewLineProjector201 V U h.symm = 1 - skewLineProjector201 U V h := by
  classical
  ext i j
  change V.projection U h.symm (Pi.single j 1) i = _
  rw [Submodule.projection_eq_self_sub_projection h]
  simp only [skewLineProjector201, LinearMap.toMatrix'_apply, Matrix.sub_apply,
    Matrix.one_apply, Pi.sub_apply, Pi.single_apply, eq_comm]

theorem skewLineProjector_idempotent201
    (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V) :
    skewLineProjector201 U V h * skewLineProjector201 U V h =
      skewLineProjector201 U V h := by
  have hp := Submodule.isIdempotentElem_projection h
  change (U.projection V h).comp (U.projection V h) = U.projection V h at hp
  change LinearMap.toMatrix' (U.projection V h) *
      LinearMap.toMatrix' (U.projection V h) = LinearMap.toMatrix' (U.projection V h)
  rw [← LinearMap.toMatrix'_comp, hp]

theorem skewLineProjector_exact_kernels201
    (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V) :
    LinearMap.ker (1 - skewLineProjector201 U V h).mulVecLin = U ∧
    LinearMap.ker (skewLineProjector201 U V h).mulVecLin = V := by
  rw [skewLineProjector_complement_mulVecLin201, skewLineProjector_mulVecLin201,
    Submodule.ker_projection, Submodule.ker_projection]
  exact ⟨rfl, rfl⟩

/-- Semilinear exchange follows from exchange of the actual two subspaces. -/
theorem skewLineProjection_semilinear201
    (σ : E ≃ₐ[k] E) (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V)
    (hσU : ∀ x ∈ U, (fun i => σ (x i)) ∈ V)
    (hσV : ∀ x ∈ V, (fun i => σ (x i)) ∈ U) (x : Fin 4 → E) :
    (fun i => σ (U.projection V h x i)) =
      V.projection U h.symm (fun i => σ (x i)) := by
  have hSum : (fun i => σ (x i)) =
      (fun i => σ (U.projection V h x i)) +
      (fun i => σ (V.projection U h.symm x i)) := by
    have hx := Submodule.projection_add_projection_eq_self h x
    funext i
    have hi := congrArg (fun y : Fin 4 → E => σ (y i)) hx
    simpa only [Pi.add_apply, map_add] using hi.symm
  rw [hSum, map_add,
    Submodule.projection_apply_of_mem_left h.symm
      (hσU _ (Submodule.projection_apply_mem h x)),
    Submodule.projection_apply_of_mem_right h.symm
      (hσV _ (Submodule.projection_apply_mem h.symm x)), add_zero]

theorem skewLineProjector_exchange201
    (σ : E ≃ₐ[k] E) (U V : Submodule E (Fin 4 → E)) (h : IsCompl U V)
    (hσU : ∀ x ∈ U, (fun i => σ (x i)) ∈ V)
    (hσV : ∀ x ∈ V, (fun i => σ (x i)) ∈ U) :
    (skewLineProjector201 U V h).map σ.toRingHom =
      1 - skewLineProjector201 U V h := by
  classical
  ext i j
  have hs : (fun m => σ ((Pi.single j (1 : E) : Fin 4 → E) m)) =
      Pi.single j 1 := by
    funext m
    by_cases hm : j = m <;> simp [Pi.single_apply, hm]
  have hi := congrFun (skewLineProjection_semilinear201 σ U V h hσU hσV
    (Pi.single j 1)) i
  rw [hs, Submodule.projection_eq_self_sub_projection h] at hi
  have hσapply (a : E) : σ.toRingHom a = σ a := rfl
  simpa only [skewLineProjector201, Matrix.map_apply, LinearMap.toMatrix'_apply,
    Matrix.sub_apply, Matrix.one_apply, Pi.sub_apply, Pi.single_apply, eq_comm, hσapply] using hi

/-- No compatible ambient frame is an input. It is constructed from the two lines. -/
theorem rankTwoConjugateSkew_exists_paired_frame201
    (σ : E ≃ₐ[k] E) (U V : Submodule E (Fin 4 → E))
    (hU : finrank E U = 2) (hV : finrank E V = 2) (hSkew : Disjoint U V)
    (hσU : ∀ x ∈ U, (fun i => σ (x i)) ∈ V)
    (hσV : ∀ x ∈ V, (fun i => σ (x i)) ∈ U) :
    let h := rankTwoSkew_isCompl201 U V hU hV hSkew
    ∃ C : Basis (Fin 4) E (Fin 4 → E),
      matchingEdgeProjectorMatrix C = skewLineProjector201 U V h ∧
      ∀ i : Fin 2, ∀ j : Fin 4,
        C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j) := by
  dsimp only
  let h := rankTwoSkew_isCompl201 U V hU hV hSkew
  have hk := skewLineProjector_exact_kernels201 U V h
  exact exists_paired_projector_frame σ (skewLineProjector201 U V h)
    (skewLineProjector_idempotent201 U V h)
    (skewLineProjector_exchange201 σ U V h hσU hσV)
    (by rw [hk.1]; exact hU) (by rw [hk.2]; exact hV)

end PfaffianDescent.QuadraticSkewRationality.OrdinaryLines201
