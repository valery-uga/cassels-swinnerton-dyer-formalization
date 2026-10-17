import PfaffianDescent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.SMul

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}

/-- Replacing any basis vector by the last frame vector is possible precisely when
all its basis coordinates are nonzero; this is the required forward implication. -/
theorem frame_coordinates_ne_zero (b : Basis (Fin n) K V) (v : V)
    (h : ∀ j : Fin n, LinearIndependent K (fun i => if i = j then v else b i)) :
    ∀ j : Fin n, b.repr v j ≠ 0 := by
  classical
  intro j hj
  let w : Fin n → V := fun i => if i = j then v else b i
  have hs : ∑ i : Fin n, b.repr v i • w i = v := by
    calc
      _ = ∑ i : Fin n, b.repr v i • b i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · subst i
          simp only [hj, zero_smul]
        · simp only [w, hij, ↓reduceIte]
      _ = v := b.sum_repr v
  let c : Fin n → K := fun i => b.repr v i - if i = j then 1 else 0
  have hc : ∑ i : Fin n, c i • w i = 0 := by
    simp only [c, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hs]
    simp only [w, ↓reduceIte, sub_self]
  have hz := (Fintype.linearIndependent_iff.mp (h j)) c hc j
  simp only [c, hj, ↓reduceIte, zero_sub, neg_eq_zero] at hz
  exact one_ne_zero hz

/-- A projective frame is an invertible linear image of the coordinate points and
`[1:⋯:1]`, with nonzero rescalings of the coordinate vectors. -/
theorem basis_frame_normalization (b : Basis (Fin n) K V) (v : V)
    (h : ∀ j : Fin n, LinearIndependent K (fun i => if i = j then v else b i)) :
    ∃ c : Fin n → K, (∀ i, c i ≠ 0) ∧
      ∃ E : (Fin n → K) ≃ₗ[K] V,
        (∀ i, E (Pi.single i 1) = c i • b i) ∧ E (fun _ => 1) = v := by
  classical
  have hc := frame_coordinates_ne_zero b v h
  let u : Fin n → Kˣ := fun i => Units.mk0 (b.repr v i) (hc i)
  let b' := b.unitsSMul u
  have hb (i : Fin n) : b' i = b.repr v i • b i := by
    change b.unitsSMul u i = _
    rw [Basis.unitsSMul_apply, Units.smul_def]
    rfl
  refine ⟨fun i => b.repr v i, hc, b'.equivFun.symm, ?_, ?_⟩
  · intro i
    rw [Basis.equivFun_symm_apply]
    simpa only [Pi.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hb i
  · rw [Basis.equivFun_symm_apply]
    simp only [one_smul, hb]
    exact b.sum_repr v

end

section
variable {K : Type*} [Field K]

/-- No four of the five homogeneous coordinate vectors are linearly dependent. -/
def FivePointGeneralPosition (p : Fin 5 → Vec K 4) : Prop :=
  ∀ e : Fin 4 → Fin 5, Function.Injective e → LinearIndependent K (p ∘ e)

private def replacementIndex (j i : Fin 4) : Fin 5 :=
  if i = j then 4 else i.castSucc

private theorem replacementIndex_injective (j : Fin 4) : Function.Injective (replacementIndex j) := by
  intro i k h
  by_cases hi : i = j <;> by_cases hk : k = j
  · exact hi.trans hk.symm
  · simp only [replacementIndex, hi, hk, ↓reduceIte] at h
    have hv := congrArg Fin.val h
    change 4 = k.val at hv
    omega
  · simp only [replacementIndex, hi, hk, ↓reduceIte] at h
    have hv := congrArg Fin.val h
    change i.val = 4 at hv
    omega
  · simp only [replacementIndex, hi, hk, ↓reduceIte] at h
    exact Fin.castSucc_injective 4 h

/-- The coordinate normalization asserted at the beginning of the appendix. -/
theorem five_point_frame_normalization (p : Fin 5 → Vec K 4) (hp : FivePointGeneralPosition p) :
    ∃ c : Fin 4 → K, (∀ i, c i ≠ 0) ∧
      ∃ E : Vec K 4 ≃ₗ[K] Vec K 4,
        (∀ i, E (Pi.single i 1) = c i • p i.castSucc) ∧ E (fun _ => 1) = p 4 := by
  classical
  have hbase : LinearIndependent K (fun i : Fin 4 => p i.castSucc) :=
    hp Fin.castSucc (Fin.castSucc_injective 4)
  let b : Basis (Fin 4) K (Vec K 4) :=
    basisOfLinearIndependentOfCardEqFinrank hbase (by simp [Vec])
  have hb (i : Fin 4) : b i = p i.castSucc := congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank hbase (by simp [Vec])) i
  have hreplace (j : Fin 4) : LinearIndependent K (fun i => if i = j then p 4 else b i) := by
    have h := hp (replacementIndex j) (replacementIndex_injective j)
    have he : p ∘ replacementIndex j = fun i => if i = j then p 4 else b i := by
      funext i
      by_cases hij : i = j <;> simp [Function.comp_apply, replacementIndex, hij, hb]
    rw [he] at h
    exact h
  obtain ⟨c, hc, E, hE, hlast⟩ := basis_frame_normalization b (p 4) hreplace
  exact ⟨c, hc, E, fun i => (hE i).trans (congrArg (c i • ·) (hb i)), hlast⟩

end
end PfaffianDescent
