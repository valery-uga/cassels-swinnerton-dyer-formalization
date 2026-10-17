import PfaffianDescent.FrameQuadraticSpan
import PfaffianDescent.GeneratorBasisChange

namespace PfaffianDescent
open MvPolynomial Module
section
variable {K : Type*} [Field K]

lemma changedFrameRelations_independent
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K) :
    LinearIndependent K (fun i : Fin 5 => E (frameRelations i)) :=
  frameRelations_independent.map' E.toLinearMap (LinearMap.ker_eq_bot.mpr E.injective)

/-- Five independent quadratic equations in a projective-frame ideal span its
entire quadratic generator space. -/
theorem frame_quadratic_generators_span
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (p : MvPolynomial (Fin 4) K), p.IsHomogeneous d → (E p).IsHomogeneous d)
    (q : Fin 5 → MvPolynomial (Fin 4) K) (hq : LinearIndependent K q)
    (hd : ∀ i, (q i).IsHomogeneous 2)
    (hI : ∀ i, q i ∈ (frameIdeal (K := K)).map E.toRingHom) :
    Submodule.span K (Set.range q) =
      Submodule.span K (Set.range (fun i : Fin 5 => E (frameRelations i))) := by
  haveI : Module.Finite K (Submodule.span K (Set.range (fun i : Fin 5 => E (frameRelations i)))) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact changed_frame_quadratic_mem_span E hE (q i) (hd i) (hI i)
  · rw [finrank_span_eq_card hq, finrank_span_eq_card (changedFrameRelations_independent E)]

/-- A change from the displayed frame quadrics to any independent quadratic
set is given by an invertible matrix over the coefficient field. -/
theorem frame_quadratic_generators_matrix
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (p : MvPolynomial (Fin 4) K), p.IsHomogeneous d → (E p).IsHomogeneous d)
    (q : Fin 5 → MvPolynomial (Fin 4) K) (hq : LinearIndependent K q)
    (hd : ∀ i, (q i).IsHomogeneous 2)
    (hI : ∀ i, q i ∈ (frameIdeal (K := K)).map E.toRingHom) :
    ∃ D : Matrix (Fin 5) (Fin 5) K, IsUnit D.det ∧
      ∀ j, q j = ∑ i, D i j • E (frameRelations i) :=
  exists_generator_basis_change _ q (changedFrameRelations_independent E) hq
    (frame_quadratic_generators_span E hE q hq hd hI).symm

end
end PfaffianDescent
