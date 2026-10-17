import PfaffianDescent.NativeArtinianObstructionCriterion316
import PfaffianDescent.NativeResidueCotangentInjectivity316
import Mathlib.RingTheory.Smooth.Local

/-! A local presentation criterion using genuine Artinian quotient tests.
The application to the geometric classifier must still construct the required
presentation and its lifts; they are explicit premises of this algebra lemma. -/
namespace PfaffianDescent
open IsLocalRing KaehlerDifferential

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]
  [IsLocalRing P] [IsNoetherianRing P]
  [Algebra.FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]

theorem formallySmooth_quotient_of_artinian_tests316 (I : Ideal P)
    (hI : I ≤ maximalIdeal P)
    (hlift : ∀ N : ℕ, 0 < N →
      ∃ l : P ⧸ I →ₐ[R] P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N,
        (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 (maximalIdeal P) I N)).comp l =
          Ideal.Quotient.factorₐ R
            (show I ≤ obstructionThinIdeal316 (maximalIdeal P) I N from le_sup_left)) :
    Algebra.FormallySmooth R (P ⧸ I) := by
  letI : IsLocalRing (P ⧸ I) := obstructionQuotient_local316 I hI
  let g : P ⧸ I →ₐ[P] ResidueField P := Ideal.Quotient.factorₐ P hI
  letI : Algebra (P ⧸ I) (ResidueField P) := g.toAlgebra
  letI : IsScalarTower P (P ⧸ I) (ResidueField P) :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have hmax : maximalIdeal (P ⧸ I) ≤ RingHom.ker (algebraMap (P ⧸ I) (ResidueField P)) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective]
    apply (Ideal.map_le_iff_le_comap).2
    intro a ha
    change Ideal.Quotient.mk (maximalIdeal P) a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  apply (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
    (R := R) (S := P ⧸ I) P (ResidueField P)
    Ideal.Quotient.mk_surjective (Ideal.fg_of_isNoetherianRing _) hmax).2
  letI : Algebra (P ⧸ I) (P ⧸ maximalIdeal P) :=
    (inferInstance : Algebra (P ⧸ I) (ResidueField P))
  letI : IsScalarTower P (P ⧸ I) (P ⧸ maximalIdeal P) :=
    (inferInstance : IsScalarTower P (P ⧸ I) (ResidueField P))
  apply residueCotangent_injective_of_relation_criterion316 (maximalIdeal P)
  intro x hD
  have hx : (x : P) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp x.property
  have he : RingHom.ker (algebraMap P (P ⧸ I)) = I := Ideal.mk_ker
  have hmem := obstruction_relation_mem_of_quotient_lifts316 I hI hlift hx hD
  have hle : maximalIdeal P * I ≤ maximalIdeal P * RingHom.ker (algebraMap P (P ⧸ I)) :=
    Ideal.mul_mono le_rfl (le_of_eq he.symm)
  exact hle hmem

end PfaffianDescent
