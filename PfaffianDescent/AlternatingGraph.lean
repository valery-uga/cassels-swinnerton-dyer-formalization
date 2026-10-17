import PfaffianDescent.GrassmannianGraph
import PfaffianDescent.AlternatingProduct

namespace PfaffianDescent
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- The triangular change of coordinates carrying the first summand to a graph. -/
def graphShear (f : M →ₗ[R] N) : (M × N) ≃ₗ[R] (M × N) where
  toFun x := (x.1, f x.1 + x.2)
  invFun x := (x.1, x.2 - f x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp [add_add_add_comm]
  map_smul' c x := by ext <;> simp [smul_add]

/-- An alternating form's blocks in coordinates adapted to the graph. -/
def alternatingGraphBlocks (f : M →ₗ[R] N) : AlternatingTwoForms R (M × N) ≃ₗ[R]
    AlternatingTwoForms R M × ((M →ₗ[R] N →ₗ[R] R) × AlternatingTwoForms R N) :=
  (AlternatingMap.domLCongr R R (Fin 2) R (graphShear f).symm).trans alternatingProductEquiv

lemma alternatingGraphBlocks_fst (f : M →ₗ[R] N) (B : AlternatingTwoForms R (M × N)) :
    (alternatingGraphBlocks f B).1 = B.compLinearMap (LinearMap.id.prod f) := by
  ext v
  change B (fun i => (v i, f (v i) + 0)) = B (fun i => (v i, f (v i)))
  simp

/-- Vanishing of the first block is exactly vanishing on the actual graph submodule. -/
lemma alternatingGraphBlocks_fst_zero_iff (f : M →ₗ[R] N) (B : AlternatingTwoForms R (M × N)) :
    (alternatingGraphBlocks f B).1 = 0 ↔ alternatingRestriction R (M × N) f.graph B = 0 := by
  rw [alternatingGraphBlocks_fst]
  constructor
  · intro h
    ext v
    have hh := DFunLike.congr_fun h (fun i => (v i).1.1)
    change B (fun i => ((v i).1.1, f (v i).1.1)) = 0 at hh
    change B (fun i => (v i).1) = 0
    convert hh using 1
    congr 1
    funext i
    exact Prod.ext rfl (v i).2
  · intro h
    ext v
    exact DFunLike.congr_fun h (fun i => ⟨(v i, f (v i)), rfl⟩)

/-- The kernel of restriction on a Grassmannian graph chart has independent
mixed and second-block coordinates. This is valid over nonreduced rings. -/
def alternatingGraphKernelEquiv (f : M →ₗ[R] N) :
    LinearMap.ker (alternatingRestriction R (M × N) f.graph) ≃ₗ[R]
      ((M →ₗ[R] N →ₗ[R] R) × AlternatingTwoForms R N) where
  toFun B := (alternatingGraphBlocks f B.1).2
  invFun t := ⟨(alternatingGraphBlocks f).symm (0, t), by
    apply (alternatingGraphBlocks_fst_zero_iff f _).mp
    rw [(alternatingGraphBlocks f).apply_symm_apply]⟩
  left_inv B := by
    apply Subtype.ext
    apply (alternatingGraphBlocks f).injective
    rw [(alternatingGraphBlocks f).apply_symm_apply]
    apply Prod.ext
    · exact ((alternatingGraphBlocks_fst_zero_iff f B.1).mpr B.2).symm
    · rfl
  right_inv t := congrArg Prod.snd ((alternatingGraphBlocks f).apply_symm_apply (0, t))
  map_add' B C := by
    change (alternatingGraphBlocks f (B.1 + C.1)).2 = _
    rw [map_add]
    rfl
  map_smul' c B := by
    change (alternatingGraphBlocks f (c • B.1)).2 = _
    rw [map_smul]
    rfl

end
end PfaffianDescent
