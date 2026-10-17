import PfaffianDescent.VoisinGenericQuadraticEvaluation

/-! Detection of the fixed quadratic frame descends along a field extension. -/

namespace PfaffianDescent

open MvPolynomial

universe u

/-- Eight extension-field points that detect every combination of the fixed
quadratic frame also detect every combination with coefficients in the
original field. This is the algebraic evaluation step needed when an
algebraic-closure witness is used on a cubic over a smaller field. -/
theorem quadraticEightFrame_detection_descends
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L) (x : Fin 8 → Fin 4 → L)
    (hdetect : ∀ c : Fin 8 → L,
      (∀ i, eval (x i)
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0) :
    ∀ c : Fin 8 → K,
      (∀ i, eval₂ b (x i)
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0 := by
  intro c hc
  have hzero : ∀ i, eval (x i)
      (homogeneousFrameMap 2 (quadraticEightFrame L)
        (fun j => b (c j))).1 = 0 := by
    intro i
    rw [← quadraticEightFrameCombination_map b c]
    simpa only [eval₂_eq_eval_map] using hc i
  have hbc := hdetect (fun j => b (c j)) hzero
  funext i
  exact (RingHom.injective b) (by simpa only [Pi.zero_apply, map_zero] using congrFun hbc i)

/-- Detection of the extended fixed frame by the eight geometric points
surjects the quadratic restriction map of the original rank-eight algebra.
The target of restriction remains the original, possibly nonsplit algebra. -/
theorem quadraticSectionRestriction_surjective_of_extendedFrameDetection
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hdetect : ∀ c : Fin 8 → L,
      (∀ i, eval (fun j => φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0) :
    Function.Surjective (homogeneousSectionRestriction (K := K) x 2) := by
  apply quadraticSectionRestriction_surjective_of_embedding_evaluations
    x hA φ
  exact quadraticEightFrame_detection_descends (algebraMap K L)
    (fun i j => φ i (x j)) hdetect

/-- If eight coordinate vectors are defined over the ground field and their
images detect the extended fixed frame, then the original vectors detect the
ground-field frame. -/
theorem quadraticEightFrame_detection_reflects
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L) (x : Fin 8 → Fin 4 → K)
    (hdetect : ∀ c : Fin 8 → L,
      (∀ i, eval (fun j => b (x i j))
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0) :
    ∀ c : Fin 8 → K,
      (∀ i, eval (x i)
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0 := by
  intro c hc
  have hzero : ∀ i, eval (fun j => b (x i j))
      (homogeneousFrameMap 2 (quadraticEightFrame L)
        (fun j => b (c j))).1 = 0 := by
    intro i
    rw [← quadraticEightFrameCombination_map b c]
    rw [MvPolynomial.eval_map]
    have hi := congrArg b (hc i)
    simpa only [map_zero, MvPolynomial.eval₂_comp, Function.comp_def] using hi
  have hbc := hdetect (fun j => b (c j)) hzero
  funext i
  apply RingHom.injective b
  simpa only [Pi.zero_apply, map_zero] using congrFun hbc i

end PfaffianDescent
