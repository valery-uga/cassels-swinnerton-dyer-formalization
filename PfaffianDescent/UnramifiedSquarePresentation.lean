import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace PfaffianDescent
open Algebra Module MvPolynomial

section
variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Finite σ] (P : Algebra.PreSubmersivePresentation R S ι σ)

/-- Every conormal differential is a linear combination of the displayed relation differentials. -/
lemma presentation_cotangentAux_mem_range (x : P.toExtension.Cotangent) :
    P.cotangentComplexAux x ∈ LinearMap.range P.aevalDifferential := by
  classical
  obtain ⟨(x : P.ker), rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  have hx : x.val ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact x.property
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hx
  refine ⟨∑ i ∈ c.support, aeval P.val (c i) • Pi.single i 1, ?_⟩
  funext j
  rw [P.cotangentComplexAux_apply]
  conv_rhs => rw [← hc]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    P.aevalDifferential_single, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    P.aeval_val_relation, zero_mul, add_zero]

/-- Unramifiedness makes the selected relation differential surjective. -/
lemma presentation_aevalDifferential_surjective [Algebra.FormallyUnramified R S] :
    Function.Surjective P.aevalDifferential := by
  have hc : Function.Surjective P.toExtension.cotangentComplex := by
    intro z
    exact (P.toExtension.exact_cotangentComplex_toKaehler z).mp (Subsingleton.elim _ _)
  have ha : Function.Surjective P.cotangentComplexAux := by
    change Function.Surjective ((Finsupp.linearEquivFunOnFinite S S σ) ∘
      (Finsupp.lcomapDomain (R := S) P.map P.map_inj) ∘ P.cotangentSpaceBasis.repr ∘
      P.toExtension.cotangentComplex)
    exact (Finsupp.linearEquivFunOnFinite S S σ).surjective.comp
      ((Finsupp.comapDomain_surjective P.map_inj).comp
        (P.cotangentSpaceBasis.repr.surjective.comp hc))
  intro y
  obtain ⟨x, rfl⟩ := ha y
  exact presentation_cotangentAux_mem_range P x

/-- For a finite pre-submersive presentation, unramifiedness forces the Jacobian to be a unit. -/
theorem presentation_jacobian_isUnit_of_unramified [Algebra.FormallyUnramified R S] :
    IsUnit P.jacobian := by
  rw [P.isUnit_jacobian_iff_aevalDifferential_bijective]
  have hs := presentation_aevalDifferential_surjective P
  exact ⟨Module.End.injective_of_surjective S (σ → S) hs, hs⟩

/-- A square presentation of an unramified algebra is étale. -/
theorem squarePresentation_etale_of_unramified [Finite ι]
    [Algebra.FormallyUnramified R S] (hdim : P.dimension = 0) : Algebra.Etale R S := by
  let Q : Algebra.SubmersivePresentation R S ι σ :=
    ⟨P, presentation_jacobian_isUnit_of_unramified P⟩
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R S :=
    Q.isStandardSmoothOfRelativeDimension hdim
  infer_instance

end
end PfaffianDescent
