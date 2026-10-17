import PfaffianDescent.Copfaffian
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace PfaffianDescent
open Module
open _root_.LinearMap (BilinForm)
open scoped BigOperators

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- An alternating form in dimension three has a nonzero radical vector. -/
theorem radical_of_finrank_three (B : BilinForm K V) (hB : B.IsAlt)
    (hdim : finrank K V = 3) : ∃ v : V, v ≠ 0 ∧ ∀ w : V, B w v = 0 := by
  let b := Module.finBasisOfFinrankEq K V hdim
  let M : Mat K 3 := fun i j => B (b i) (b j)
  have hdiag : ∀ i, M i i = 0 := fun i => hB (b i)
  have hskew : ∀ i j, M j i = -M i j := fun i j => (hB.neg_eq (b i) (b j)).symm
  have hdet : M.det = 0 := by
    rw [Matrix.det_fin_three]
    rw [hdiag 0, hdiag 1, hdiag 2, hskew 0 1, hskew 0 2, hskew 1 2]
    ring
  obtain ⟨u, hu, hMu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let v : V := b.equivFun.symm u
  have hv : v ≠ 0 := by
    intro hz
    apply hu
    exact b.equivFun.symm.injective (hz.trans (map_zero _).symm)
  refine ⟨v, hv, ?_⟩
  have hb : ∀ i, B (b i) v = 0 := by
    intro i
    have hi := congrFun hMu i
    simpa [v, Basis.equivFun_symm_apply, Matrix.mulVec, dotProduct, M, mul_comm] using hi
  have hz : B.flip v = 0 := b.ext hb
  intro w
  exact LinearMap.congr_fun hz w

/-- The annihilator has dimension three. -/
theorem finrank_annihilator_three (hdim : finrank K V = 6)
    (W : Submodule K V) (hW : finrank K W = 3) :
    finrank K W.dualAnnihilator = 3 := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

/-- Four vectors in a three-dimensional space have a nontrivial relation. -/
theorem four_vectors_dependent (hdim : finrank K V = 3) (φ : Fin 4 → V) :
    ∃ q : Fin 4 → K, q ≠ 0 ∧ ∑ i, q i • φ i = 0 := by
  have hdep : ¬ LinearIndependent K φ := by
    intro h
    have hc := h.fintype_card_le_finrank
    simp only [Fintype.card_fin, hdim] at hc
    omega
  obtain ⟨q, hq, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨q, ?_, hq⟩
  intro hz
  exact hi (congrFun hz i)

/-- Four covectors annihilating a three-space in a six-space are dependent. -/
theorem four_annihilating_covectors (hdim : finrank K V = 6)
    (W : Submodule K V) (hW : finrank K W = 3)
    (φ : Fin 4 → Module.Dual K V) (hφ : ∀ i, φ i ∈ W.dualAnnihilator) :
    ∃ q : Fin 4 → K, q ≠ 0 ∧ ∑ i, q i • φ i = 0 := by
  let ψ : Fin 4 → W.dualAnnihilator := fun i => ⟨φ i, hφ i⟩
  obtain ⟨q, hq, heq⟩ := four_vectors_dependent (finrank_annihilator_three hdim W hW) ψ
  refine ⟨q, hq, ?_⟩
  have hh := congrArg W.dualAnnihilator.subtype heq
  simpa only [map_sum, map_smul, map_zero, Submodule.subtype_apply, ψ] using hh

/-- The radical-vector construction of Step 1, stated for bilinear forms.
The common isotropic space is an explicit geometric input to this lemma. -/
theorem singular_combination_of_isotropic_three_space
    (hdim : finrank K V = 6) (B : Fin 4 → BilinForm K V)
    (hB : (B 3).IsAlt) (W : Submodule K V) (hW : finrank K W = 3)
    (hiso : ∀ i : Fin 3, ∀ v w : W, B i.castSucc v w = 0) :
    ∃ (q : Fin 4 → K) (v : V), q ≠ 0 ∧ v ≠ 0 ∧
      ∀ w : V, ∑ i, q i * B i w v = 0 := by
  obtain ⟨v, hv, hrad⟩ := radical_of_finrank_three ((B 3).restrict W)
    (fun w => hB w) hW
  let φ : Fin 4 → Module.Dual K V := fun i => (B i).flip v
  have hφ : ∀ i, φ i ∈ W.dualAnnihilator := by
    intro i
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    change B i w v = 0
    fin_cases i
    · exact hiso 0 ⟨w, hw⟩ v
    · exact hiso 1 ⟨w, hw⟩ v
    · exact hiso 2 ⟨w, hw⟩ v
    · exact hrad ⟨w, hw⟩
  obtain ⟨q, hq, heq⟩ := four_annihilating_covectors hdim W hW φ hφ
  refine ⟨q, v, hq, ?_, ?_⟩
  · intro hz
    exact hv (Subtype.ext hz)
  · intro w
    have hh := LinearMap.congr_fun heq w
    simpa [φ] using hh

end
end PfaffianDescent
