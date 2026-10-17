import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Kaehler.Basic

/-! A difference of square-zero lifts cannot kill a detected relation whose
differential vanishes modulo the ideal annihilating the target kernel. -/
namespace PfaffianDescent
open KaehlerDifferential

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

theorem obstruction_derivation_vanishes316
    {M : Type*} [AddCommGroup M] [Module P M] [Module R M] [IsScalarTower R P M]
    (m : Ideal P) (d : Derivation R P M)
    (hann : ∀ a ∈ m, ∀ y : M, a • y = 0)
    {x : P} (hx : D R P x ∈ m • (⊤ : Submodule P Ω[P⁄R])) :
    d x = 0 := by
  rw [← d.liftKaehlerDifferential_comp_D]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    rw [map_smul, hann a ha]
  · intro y z hy hz
    rw [map_add, hy, hz, add_zero]

theorem obstruction_squareZeroLift_preserves_relation316
    {B : Type*} [CommRing B] [Algebra R B] [Algebra P B] [IsScalarTower R P B]
    (J : Ideal B) (hJ : J ^ 2 = ⊥) (m : Ideal P)
    (hann : ∀ a ∈ m, ∀ y : J, a • y = 0)
    (f : P →ₐ[R] B)
    (he : (Ideal.Quotient.mkₐ R J).comp f = IsScalarTower.toAlgHom R P (B ⧸ J))
    {x : P} (hx : D R P x ∈ m • (⊤ : Submodule P Ω[P⁄R])) :
    f x = algebraMap P B x := by
  have hd := obstruction_derivation_vanishes316 m
    (derivationToSquareZeroOfLift J hJ f he) hann hx
  have hz : (derivationToSquareZeroOfLift J hJ f he x : B) = 0 :=
    congrArg (fun y : J => (y : B)) hd
  rw [derivationToSquareZeroOfLift_apply] at hz
  exact sub_eq_zero.mp hz

theorem obstruction_squareZeroLift_impossible316
    {B : Type*} [CommRing B] [Algebra R B] [Algebra P B] [IsScalarTower R P B]
    (J : Ideal B) (hJ : J ^ 2 = ⊥) (m : Ideal P)
    (hann : ∀ a ∈ m, ∀ y : J, a • y = 0)
    (f : P →ₐ[R] B)
    (he : (Ideal.Quotient.mkₐ R J).comp f = IsScalarTower.toAlgHom R P (B ⧸ J))
    {x : P} (hx : D R P x ∈ m • (⊤ : Submodule P Ω[P⁄R]))
    (hf : f x = 0) (hne : algebraMap P B x ≠ 0) : False := by
  exact hne ((obstruction_squareZeroLift_preserves_relation316 J hJ m hann f he hx).symm.trans hf)

end PfaffianDescent
