import PfaffianDescent.NativeArtinianObstructionQuotient316
import PfaffianDescent.NativeArtinianObstructionDerivation316

/-! The actual quotient test has no lift when it detects a relation with
vanishing residue differential. All kernel compatibility is proved internally. -/
namespace PfaffianDescent
open KaehlerDifferential

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

theorem obstructionQuotient_kernel_smul_zero316 (m I : Ideal P) (N : ℕ)
    (a : P) (ha : a ∈ m)
    (y : RingHom.ker (obstructionQuotientReduction316 m I N)) : a • y = 0 := by
  apply Subtype.ext
  change Ideal.Quotient.mk (obstructionThickIdeal316 m I N) a * (y : P ⧸ _) = 0
  apply Ideal.mem_bot.mp
  rw [← obstructionQuotientReduction_kernel_annihilated316 m I N]
  exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) y.property

theorem obstructionQuotient_no_lift316 (m I : Ideal P) (hI : I ≤ m) (N : ℕ)
    {x : P} (hx : x ∈ I)
    (hD : D R P x ∈ m • (⊤ : Submodule P Ω[P⁄R]))
    (hne : x ∉ obstructionThickIdeal316 m I N)
    (l : P ⧸ I →ₐ[R] P ⧸ obstructionThickIdeal316 m I N)
    (hl : (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 m I N)).comp l =
      Ideal.Quotient.factorₐ R
        (show I ≤ obstructionThinIdeal316 m I N from le_sup_left)) : False := by
  let B := P ⧸ obstructionThickIdeal316 m I N
  let J : Ideal B := RingHom.ker (obstructionQuotientReduction316 m I N)
  let f : P →ₐ[R] B := l.comp (Ideal.Quotient.mkₐ R I)
  have he : (Ideal.Quotient.mkₐ R J).comp f =
      IsScalarTower.toAlgHom R P (B ⧸ J) := by
    ext a
    apply Ideal.Quotient.eq.mpr
    change obstructionQuotientReduction316 m I N
      (f a - Ideal.Quotient.mk (obstructionThickIdeal316 m I N) a) = 0
    rw [map_sub, obstructionQuotientReduction_mk316]
    apply sub_eq_zero.mpr
    exact congrArg (fun g : P ⧸ I →ₐ[R] P ⧸ obstructionThinIdeal316 m I N =>
      g (Ideal.Quotient.mk I a)) hl
  have hf : f x = 0 := by
    change l (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  exact obstruction_squareZeroLift_impossible316 J
    (obstructionQuotientReduction_kernel_sq_zero316 m I N hI) m
    (obstructionQuotient_kernel_smul_zero316 m I N) f he hD hf
    (obstructionQuotient_relation_nonzero316 m I N hne)

end PfaffianDescent
