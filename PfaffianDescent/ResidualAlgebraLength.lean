import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Colon

namespace PfaffianDescent
open Module
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- The residual ideal of an ideal in a finite algebra is its annihilator. -/
abbrev residualAlgebraIdeal (P : Ideal A) : Ideal A := Module.annihilator A P

lemma residualAlgebraIdeal_eq_colon (P : Ideal A) :
    residualAlgebraIdeal P = (⊥ : Ideal A).colon (P : Set A) :=
  (Submodule.bot_colon (N := P)).symm

/-- A one-dimensional ideal has a one-dimensional residual quotient. This
constructs the residual algebra even if the ambient algebra is nonreduced. -/
theorem residual_quotient_finrank_one (P : Ideal A) (hP : finrank K P = 1) :
    finrank K (A ⧸ residualAlgebraIdeal P) = 1 := by
  have : Module.Finite K P := Module.Finite.of_injective
    (P.restrictScalars K).subtype (Submodule.injective_subtype _)
  let act : A →ₐ[K] Module.End K P := Algebra.lsmul K K P
  have hk : RingHom.ker act.toRingHom = residualAlgebraIdeal P := by
    ext a
    simp only [RingHom.mem_ker, residualAlgebraIdeal, Module.mem_annihilator]
    exact LinearMap.ext_iff
  let g : A ⧸ residualAlgebraIdeal P →ₐ[K] Module.End K P :=
    Ideal.Quotient.liftₐ _ act (fun a ha => RingHom.mem_ker.mp (hk.symm ▸ ha))
  have hg : Function.Injective g :=
    RingHom.lift_injective_of_ker_le_ideal _ _ hk.le
  have hle : finrank K (A ⧸ residualAlgebraIdeal P) ≤ 1 := by
    have h := LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) hg
    simpa only [Module.End, Module.finrank_linearMap, hP, one_mul] using h
  have hPnt : Nontrivial P := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hann : residualAlgebraIdeal P ≠ ⊤ := by
    intro he
    have hsub := (Module.annihilator_eq_top_iff (R := A) (M := P)).mp he
    exact not_subsingleton P hsub
  have : Nontrivial (A ⧸ residualAlgebraIdeal P) := Ideal.Quotient.nontrivial_iff.mpr hann
  have hpos : 0 < finrank K (A ⧸ residualAlgebraIdeal P) := Module.finrank_pos
  omega

/-- Removing a quotient of codimension one from a finite algebra leaves an
annihilator residual algebra of rank one.  This needs no Gorenstein or
Frobenius hypothesis: the defining ideal itself is one-dimensional. -/
theorem residual_algebra_rank_one_of_codimension_one (P : Ideal A) (n : ℕ)
    (hA : finrank K A = n + 1) (hP : finrank K (A ⧸ P) = n) :
    finrank K (A ⧸ residualAlgebraIdeal P) = 1 := by
  have h := (P.restrictScalars K).finrank_quotient_add_finrank
  change finrank K (A ⧸ P) + finrank K P = finrank K A at h
  apply residual_quotient_finrank_one P
  omega

/-- Removing a length-five quotient from a length-six algebra leaves the
actual annihilator quotient of length one. -/
theorem residual_algebra_six_minus_five (P : Ideal A)
    (hA : finrank K A = 6) (hP : finrank K (A ⧸ P) = 5) :
    finrank K (A ⧸ residualAlgebraIdeal P) = 1 := by
  simpa using residual_algebra_rank_one_of_codimension_one P 5 hA hP

end
end PfaffianDescent
