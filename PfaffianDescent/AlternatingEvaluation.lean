import PfaffianDescent.AlternatingCoordinates

namespace PfaffianDescent
open Module
section
variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [LinearOrder I] [Fintype (Set.powersetCard I 2)]

/-- Evaluation in exterior-power coordinates is a sum of two-by-two minors. -/
lemma alternating_evaluation_coordinates (b : Basis I R V) (B : AlternatingTwoForms R V)
    (v : Fin 2 → V) :
    B v = ∑ s : Set.powersetCard I 2,
      (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (v i)).det *
        alternatingCoordinates b B s := by
  let L := exteriorPower.alternatingMapLinearEquiv (R := R) (n := 2) B
  have h := congrArg L ((b.exteriorPower 2).sum_repr (exteriorPower.ιMulti R 2 v))
  simp only [map_sum, map_smul, smul_eq_mul, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti] at h
  simpa only [L, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    alternatingCoordinates, LinearEquiv.trans_apply, Basis.constr_symm_apply] using h.symm

/-- Reconstructing a form from its coefficients uses the same polynomial minor formula. -/
lemma alternatingCoordinates_symm_evaluation (b : Basis I R V)
    (c : Set.powersetCard I 2 → R) (v : Fin 2 → V) :
    (alternatingCoordinates b).symm c v = ∑ s : Set.powersetCard I 2,
      (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (v i)).det * c s := by
  rw [alternating_evaluation_coordinates b, (alternatingCoordinates b).apply_symm_apply]

end

section
variable {R S I : Type*} [CommRing R] [CommRing S]
    [LinearOrder I] [Fintype I] [Fintype (Set.powersetCard I 2)]

/-- Reconstructed coordinate forms commute with every homomorphism of coefficient rings. -/
lemma alternatingCoordinates_symm_map (φ : R →+* S) (c : Set.powersetCard I 2 → R)
    (v : Fin 2 → I → R) :
    (alternatingCoordinates (Pi.basisFun S I)).symm (φ ∘ c) (fun i j => φ (v i j)) =
      φ ((alternatingCoordinates (Pi.basisFun R I)).symm c v) := by
  rw [alternatingCoordinates_symm_evaluation, alternatingCoordinates_symm_evaluation,
    map_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [map_mul, Function.comp_apply, Basis.coord_apply, Pi.basisFun_repr]
  rw [RingHom.map_det]
  rfl

end
end PfaffianDescent
