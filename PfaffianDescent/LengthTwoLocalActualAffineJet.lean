import PfaffianDescent.LengthTwoLocalDualClassification
import PfaffianDescent.QuarticInfinitesimalPoints

/-! Tangent extraction from an ACTUAL surjective affine coordinate map of any
local length-two algebra. The dual presentation and nonzero tangent are both
constructed internally; neither is a public geometric certificate. -/

noncomputable section
namespace PfaffianDescent
open MvPolynomial TrivSqZeroExt
universe u
variable {K A : Type u} [Field K] [IsAlgClosed K]
  [CommRing A] [Algebra K A] [FiniteDimensional K A] [IsLocalRing A]

/-- Every supplied affine closed immersion with local length-two coordinate
algebra is its own actual first-order jet, under an internally derived dual
algebra identification. -/
theorem lengthTwoLocal_actual_affine_jet
    (hA : Module.finrank K A = 2)
    (f : MvPolynomial (Fin 3) K →ₐ[K] A) (hf : Function.Surjective f) :
    ∃ (e : A ≃ₐ[K] DualNumber K) (p v : Fin 3 → K),
      v ≠ 0 ∧ e.toAlgHom.comp f = QuarticNet.affineFirstJet p v := by
  obtain ⟨e0⟩ := lengthTwoLocal_dual_equiv hA
  let e := e0.symm
  let phi : MvPolynomial (Fin 3) K →ₐ[K] DualNumber K := e.toAlgHom.comp f
  let p : Fin 3 → K := fun i => (phi (X i)).fst
  let v : Fin 3 → K := fun i => (phi (X i)).snd
  have hjet : phi = QuarticNet.affineFirstJet p v := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [QuarticNet.affineFirstJet, MvPolynomial.aeval_X]
    apply TrivSqZeroExt.ext <;> simp [p, v]
  have hv : v ≠ 0 := by
    intro hv0
    have hsnd (i : Fin 3) : (phi (X i)).snd = 0 := congrFun hv0 i
    have hconstant : phi = (TrivSqZeroExt.inlAlgHom K K K).comp (aeval p) := by
      apply MvPolynomial.algHom_ext
      intro i
      apply TrivSqZeroExt.ext <;> simp [p, hsnd]
    have hsurj : Function.Surjective phi := e.surjective.comp hf
    obtain ⟨q, hq⟩ := hsurj (TrivSqZeroExt.inr (1 : K))
    rw [hconstant] at hq
    have h := congrArg TrivSqZeroExt.snd hq
    exact zero_ne_one (by simpa using h)
  exact ⟨e, p, v, hv, hjet⟩

/-- The equality of affine jets also identifies their ENTIRE scheme-theoretic
coordinate kernels. It retains the given nilpotent structure. -/
theorem lengthTwoLocal_actual_affine_jet_kernel
    (hA : Module.finrank K A = 2)
    (f : MvPolynomial (Fin 3) K →ₐ[K] A) (hf : Function.Surjective f) :
    ∃ p v : Fin 3 → K, v ≠ 0 ∧
      RingHom.ker f.toRingHom = RingHom.ker (QuarticNet.affineFirstJet p v).toRingHom := by
  obtain ⟨e, p, v, hv, he⟩ := lengthTwoLocal_actual_affine_jet hA f hf
  refine ⟨p, v, hv, ?_⟩
  ext q
  change f q = 0 ↔ QuarticNet.affineFirstJet p v q = 0
  rw [← he]
  exact ⟨fun h => by simp [h], fun h => e.injective (by simpa using h)⟩

end PfaffianDescent
