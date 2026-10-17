import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Squared-ideal equations preserve the local cotangent space

The Coray full-jet condition must ultimately say that a selected equation lies
in the square of the surface point ideal. This module proves the algebraic
consequence for the actual quotient cotangent map: quotienting by equations in
that square leaves the cotangent space unchanged. This is a prerequisite for
turning a double point on the surface section into a normalization defect.

STATUS: source draft, UNVERIFIED. Root owns all compiler checks.
-/

namespace PfaffianDescent.Coray

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- A surjective ring map whose kernel is inside `J²` induces a bijection on
the actual ideal cotangent modules, provided `I` is the image ideal. -/
theorem mapCotangent_bijective_of_kernel_le_square
    (hsurj : Function.Surjective (algebraMap A B))
    {I : Ideal B} {J : Ideal A}
    (heq : I.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ J)
    (hker : RingHom.ker (algebraMap A B) ≤ J ^ 2) :
    Function.Bijective
      (Ideal.mapCotangent J I (Algebra.ofId A B)
        (le_of_le_of_eq le_sup_right heq.symm)) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [Ideal.mapCotangent_ker_of_surjective hsurj heq]
    apply le_antisymm ?_ bot_le
    rintro x ⟨y, hy, rfl⟩
    change (y : A) ∈ RingHom.ker (algebraMap A B) ⊓ J at hy
    rw [Submodule.mem_bot, Ideal.toCotangent_eq_zero]
    exact hker (Ideal.mem_inf.mp hy).1
  · exact Ideal.mapCotangent_surjective_of_comap_eq hsurj heq

/-- Apply the preceding statement to the literal quotient by an ideal lying
in `J²`. The target ideal is the actual image of `J` in `A/I`. -/
theorem quotient_mapCotangent_bijective_of_le_square
    (I J : Ideal A) (hI : I ≤ J ^ 2) :
    ∃ h : J ≤ (J.map (Ideal.Quotient.mk I)).comap (Algebra.ofId A (A ⧸ I)),
      Function.Bijective
        (Ideal.mapCotangent J (J.map (Ideal.Quotient.mk I))
          (Algebra.ofId A (A ⧸ I)) h) := by
  have heq :
      (J.map (Ideal.Quotient.mk I)).comap (algebraMap A (A ⧸ I)) =
        RingHom.ker (algebraMap A (A ⧸ I)) ⊔ J := by
    change (J.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) =
      RingHom.ker (Ideal.Quotient.mk I) ⊔ J
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_comm]
  refine ⟨le_of_le_of_eq le_sup_right heq.symm, ?_⟩
  apply mapCotangent_bijective_of_kernel_le_square
    Ideal.Quotient.mk_surjective heq
  change RingHom.ker (Ideal.Quotient.mk I) ≤ J ^ 2
  rwa [Ideal.mk_ker]

/-- A single equation in the squared point ideal is the case used for the
selected cubic-surface curve. -/
theorem principal_quotient_mapCotangent_bijective_of_mem_square
    (J : Ideal A) (q : A) (hq : q ∈ J ^ 2) :
    ∃ h : J ≤ (J.map (Ideal.Quotient.mk (Ideal.span {q}))).comap
        (Algebra.ofId A (A ⧸ Ideal.span {q})),
      Function.Bijective
        (Ideal.mapCotangent J (J.map (Ideal.Quotient.mk (Ideal.span {q})))
          (Algebra.ofId A (A ⧸ Ideal.span {q})) h) := by
  apply quotient_mapCotangent_bijective_of_le_square
  apply Ideal.span_le.mpr
  intro r hr
  rcases Set.mem_singleton_iff.mp hr with rfl
  exact hq

end PfaffianDescent.Coray
