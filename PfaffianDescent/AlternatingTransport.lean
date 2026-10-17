import PfaffianDescent.AlternatingRestriction

namespace PfaffianDescent
section
variable {R V V' V'' : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']
    [AddCommGroup V''] [Module R V'']

/-- Transport an alternating form with an ambient change of coordinates. -/
def alternatingTransport (e : V ≃ₗ[R] V') :
    AlternatingTwoForms R V ≃ₗ[R] AlternatingTwoForms R V' :=
  AlternatingMap.domLCongr R R (Fin 2) R e

lemma alternatingTransport_apply (e : V ≃ₗ[R] V') (B : AlternatingTwoForms R V)
    (v : Fin 2 → V') : alternatingTransport e B v = B (e.symm ∘ v) := rfl

lemma alternatingTransport_trans (e : V ≃ₗ[R] V') (d : V' ≃ₗ[R] V'') :
    (alternatingTransport e).trans (alternatingTransport d) = alternatingTransport (e.trans d) := rfl

lemma alternatingTransport_symm (e : V ≃ₗ[R] V') :
    (alternatingTransport e).symm = alternatingTransport e.symm := rfl

/-- Transport preserves vanishing on the corresponding actual submodules. -/
lemma alternatingTransport_isotropic (e : V ≃ₗ[R] V')
    (W : Submodule R V) (W' : Submodule R V') (hW : W.map e.toLinearMap = W')
    (B : AlternatingTwoForms R V) (hB : alternatingRestriction R V W B = 0) :
    alternatingRestriction R V' W' (alternatingTransport e B) = 0 := by
  ext v
  have hv (i : Fin 2) : e.symm (v i).1 ∈ W := by
    have hi : (v i).1 ∈ W.map e.toLinearMap := hW.symm ▸ (v i).2
    obtain ⟨x, hx, he⟩ := hi
    rw [← he]
    change e.symm (e x) ∈ W
    rw [e.symm_apply_apply]
    exact hx
  exact DFunLike.congr_fun hB (fun i => ⟨e.symm (v i).1, hv i⟩)

lemma submodule_map_equiv_reverse (e : V ≃ₗ[R] V')
    (W : Submodule R V) (W' : Submodule R V') (hW : W.map e.toLinearMap = W') :
    W'.map e.symm.toLinearMap = W := by
  rw [← hW, ← Submodule.map_comp]
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  rw [he, Submodule.map_id]

/-- Ambient coordinate changes identify the actual restriction kernels linearly. -/
def alternatingKernelTransportEquiv (e : V ≃ₗ[R] V')
    (W : Submodule R V) (W' : Submodule R V') (hW : W.map e.toLinearMap = W') :
    LinearMap.ker (alternatingRestriction R V W) ≃ₗ[R]
      LinearMap.ker (alternatingRestriction R V' W') where
  toFun B := ⟨alternatingTransport e B.1, alternatingTransport_isotropic e W W' hW B.1 B.2⟩
  invFun B := ⟨alternatingTransport e.symm B.1, alternatingTransport_isotropic e.symm W' W
    (submodule_map_equiv_reverse e W W' hW) B.1 B.2⟩
  left_inv B := Subtype.ext ((alternatingTransport e).symm_apply_apply B.1)
  right_inv B := Subtype.ext ((alternatingTransport e).apply_symm_apply B.1)
  map_add' B C := Subtype.ext ((alternatingTransport e).map_add B.1 C.1)
  map_smul' c B := Subtype.ext ((alternatingTransport e).map_smul c B.1)

lemma alternatingKernelTransportEquiv_apply (e : V ≃ₗ[R] V')
    (W : Submodule R V) (W' : Submodule R V') (hW : W.map e.toLinearMap = W')
    (B : LinearMap.ker (alternatingRestriction R V W)) :
    (alternatingKernelTransportEquiv e W W' hW B).1 = alternatingTransport e B.1 := rfl

/-- The restriction-kernel identifications satisfy the cocycle identity. -/
lemma alternatingKernelTransportEquiv_trans (e : V ≃ₗ[R] V') (d : V' ≃ₗ[R] V'')
    (W : Submodule R V) (W' : Submodule R V') (W'' : Submodule R V'')
    (hW : W.map e.toLinearMap = W') (hW' : W'.map d.toLinearMap = W'')
    (hW'' : W.map (e.trans d).toLinearMap = W'') :
    (alternatingKernelTransportEquiv e W W' hW).trans
      (alternatingKernelTransportEquiv d W' W'' hW') =
      alternatingKernelTransportEquiv (e.trans d) W W'' hW'' := by
  apply LinearEquiv.ext
  intro B
  apply Subtype.ext
  rfl

end
end PfaffianDescent
