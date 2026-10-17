import PfaffianDescent.MatchingProjectorIntersectionGaloisStability
import Mathlib.FieldTheory.Normal.Basic

/-! SOURCE ONLY, UNVERIFIED. Restricting the actual K-Galois action to the
SAME normal E proves its projector-pair action. The lift is constructed by
normal extension, never supplied as a final field-of-definition certificate. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

theorem intermediateMatchingProjector_galois_pair
    (E : IntermediateField k K) [Normal k E]
    (P : Matrix (Fin 4) (Fin 4) E)
    (hPair : ∀ g : K ≃ₐ[k] K,
      (P.map E.val.toRingHom).map g.toRingHom = P.map E.val.toRingHom ∨
      (P.map E.val.toRingHom).map g.toRingHom = 1 - P.map E.val.toRingHom)
    (sigma : E ≃ₐ[k] E) :
    P.map sigma.toRingHom = P ∨ P.map sigma.toRingHom = 1 - P := by
  obtain ⟨g, hg⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E) (E := K) sigma
  have hLift (z : E) : E.val (sigma z) = g (E.val z) := by
    change algebraMap E K (sigma z) = g (algebraMap E K z)
    rw [← hg]
    exact AlgEquiv.restrictNormal_commutes g E z
  rcases hPair g with h | h
  · apply Or.inl
    apply Matrix.ext
    intro m n
    apply E.val.injective
    change E.val (sigma (P m n)) = E.val (P m n)
    rw [hLift]
    exact congrFun (congrFun h m) n
  · apply Or.inr
    apply Matrix.ext
    intro m n
    apply E.val.injective
    change E.val (sigma (P m n)) = E.val ((1 - P) m n)
    rw [hLift]
    have hm := congrFun (congrFun h m) n
    by_cases hmn : m = n
    all_goals simpa [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, hmn] using hm

end PfaffianDescent.QuarticNet
