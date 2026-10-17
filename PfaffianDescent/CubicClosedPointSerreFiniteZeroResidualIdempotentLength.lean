import PfaffianDescent.FiniteEtaleResidualDisjoint
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open Module
namespace PfaffianDescent

theorem cubicClosedPointSerreFiniteZeroResidual_idempotent_finrank
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (e : A) (he : IsIdempotentElem e) (N d : ℕ)
    (hA : finrank K A = N)
    (hZ : finrank K (A ⧸ Ideal.span ({e} : Set A)) = d) :
    finrank K (A ⧸ residualAlgebraIdeal (Ideal.span ({e} : Set A))) = N - d := by
  let P : Ideal A := Ideal.span {e}
  let m : A →ₗ[K] P :=
    { toFun := fun a => ⟨a * e, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (add_mul a b e)
      map_smul' := fun r a => Subtype.ext (smul_mul_assoc r a e) }
  have hm : Function.Surjective m := by
    intro x
    refine ⟨x, Subtype.ext ?_⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
    change (x : A) * e = x
    rw [← ha, mul_assoc, he.eq]
  have hk : LinearMap.ker m = (residualAlgebraIdeal P).restrictScalars K := by
    ext a
    simp only [LinearMap.mem_ker]
    change m a = 0 ↔ a ∈ residualAlgebraIdeal (Ideal.span {e})
    rw [residualAlgebraIdeal, Submodule.mem_annihilator_span_singleton]
    exact Subtype.ext_iff
  have hdim := (P.restrictScalars K).finrank_quotient_add_finrank
  change finrank K (A ⧸ P) + finrank K P = finrank K A at hdim
  have hr := (m.quotKerEquivOfSurjective hm).finrank_eq
  rw [hk] at hr
  change finrank K (A ⧸ residualAlgebraIdeal P) = finrank K P at hr
  change finrank K (A ⧸ residualAlgebraIdeal P) = N - d
  rw [hr]
  change finrank K (A ⧸ P) = d at hZ
  omega

end PfaffianDescent
