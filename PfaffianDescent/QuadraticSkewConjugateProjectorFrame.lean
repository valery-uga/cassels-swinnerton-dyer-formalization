import PfaffianDescent.IdempotentTwoKernelFrame
import PfaffianDescent.QuadraticConjugateDescent
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
/-! SOURCE ONLY / UNVERIFIED. A paired semilinear frame is constructed
from the actual exchanged projector kernels. The two bases and all frame
certificates are outputs, not additional inputs of the matching branch. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.PairedFrame
open Module
open QuarticNet
universe u
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

theorem mapped_complement_eq_of_exchange
    (σ : E ≃ₐ[k] E) (P : Matrix (Fin 4) (Fin 4) E)
    (hP : P.map σ.toRingHom = 1 - P) :
    (1 - P).map σ.toRingHom = P := by
  have hmap : (1 - P).map σ.toRingHom = 1 - P.map σ.toRingHom := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  rw [hmap, hP]
  abel

def conjugateLeftKernel
    (σ : E ≃ₐ[k] E) (P : Matrix (Fin 4) (Fin 4) E)
    (hP : P.map σ.toRingHom = 1 - P) :
    LinearMap.ker (1 - P).mulVecLin →+ LinearMap.ker P.mulVecLin where
  toFun v := ⟨fun i => σ (v.1 i), by
    have hv : (1 - P).mulVec v.1 = 0 := v.2
    change P.mulVec (fun i => σ (v.1 i)) = 0
    ext i
    have h := (RingHom.map_mulVec σ.toRingHom (1 - P) v.1 i).symm
    rw [mapped_complement_eq_of_exchange σ P hP, hv, Pi.zero_apply, map_zero] at h
    exact h⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    exact map_zero σ
  map_add' v w := by
    apply Subtype.ext
    funext i
    exact map_add σ (v.1 i) (w.1 i)

theorem conjugateLeftKernel_injective
    (σ : E ≃ₐ[k] E) (P : Matrix (Fin 4) (Fin 4) E)
    (hP : P.map σ.toRingHom = 1 - P) :
    Function.Injective (conjugateLeftKernel σ P hP) := by
  intro v w h
  apply Subtype.ext
  funext i
  apply σ.injective
  exact congrFun (congrArg Subtype.val h) i

theorem conjugateLeftKernel_smul
    (σ : E ≃ₐ[k] E) (P : Matrix (Fin 4) (Fin 4) E)
    (hP : P.map σ.toRingHom = 1 - P)
    (a : E) (v : LinearMap.ker (1 - P).mulVecLin) :
    conjugateLeftKernel σ P hP (a • v) = σ a • conjugateLeftKernel σ P hP v := by
  apply Subtype.ext
  funext i
  exact map_mul σ a (v.1 i)

/-- Conjugating a basis of the first line produces the basis of the second
line; they are assembled into a basis of the original ambient vector space. -/
theorem exists_paired_projector_frame
    (σ : E ≃ₐ[k] E) (P : Matrix (Fin 4) (Fin 4) E)
    (hIdem : P * P = P) (hExchange : P.map σ.toRingHom = 1 - P)
    (hLeft : finrank E (LinearMap.ker (1 - P).mulVecLin) = 2)
    (hRight : finrank E (LinearMap.ker P.mulVecLin) = 2) :
    ∃ C : Basis (Fin 4) E (Fin 4 → E),
      matchingEdgeProjectorMatrix C = P ∧
      ∀ i : Fin 2, ∀ j : Fin 4,
        C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j) := by
  classical
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker (1 - P).mulVecLin) hLeft
  let j := conjugateLeftKernel σ P hExchange
  have hli : LinearIndependent E (fun i => j (b i)) := by
    exact b.linearIndependent.map_of_surjective_injectiveₛ σ j σ.surjective
      (conjugateLeftKernel_injective σ P hExchange)
      (conjugateLeftKernel_smul σ P hExchange)
  let c := basisOfLinearIndependentOfCardEqFinrank hli
    (by simpa only [Fintype.card_fin] using hRight.symm)
  have hc : ∀ i, c i = j (b i) := by
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli
      (by simpa only [Fintype.card_fin] using hRight.symm)) i
  let C := idempotentTwoKernelFrame P hIdem b c
  refine ⟨C, idempotentTwoKernelFrame_projector P hIdem b c, ?_⟩
  intro i m
  rw [show C (Fin.natAdd 2 i) = (c i : Fin 4 → E) from
    idempotentTwoKernelFrame_right P hIdem b c i,
    show C (Fin.castAdd 2 i) = (b i : Fin 4 → E) from
    idempotentTwoKernelFrame_left P hIdem b c i, hc i]
  rfl

/-- In the actual manuscript matching branch, idempotence and both kernel
dimensions are derived from the existing original geometric projector. -/
theorem actual_matching_exists_paired_projector_frame
    {K : Type u} [Field K] [Algebra k K]
    (E : IntermediateField k K) (P : Matrix (Fin 4) (Fin 4) E)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B)
    (σ : E ≃ₐ[k] E) (hExchange : P.map σ.toRingHom = 1 - P) :
    ∃ C : Basis (Fin 4) E (Fin 4 → E),
      matchingEdgeProjectorMatrix C = P ∧
      ∀ i : Fin 2, ∀ j : Fin 4,
        C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j) := by
  exact exists_paired_projector_frame σ P
    (intermediateMatchingProjector_idempotent E P B hP) hExchange
    (intermediateMatchingLine_kernel_rank_two E P B hP)
    (intermediateMatchingOtherLine_kernel_rank_two E P B hP)

end PfaffianDescent.QuadraticSkewRationality.PairedFrame
