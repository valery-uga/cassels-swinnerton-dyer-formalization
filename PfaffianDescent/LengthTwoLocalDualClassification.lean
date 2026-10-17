import Mathlib.Tactic.Ring
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A universal classification of EVERY local length-two algebra with rational
residue. The residue map itself is derived internally over an algebraically
closed field. This does not assert that an arbitrary rank-eight ground scheme
has already been decomposed into four length-two local algebras. -/

noncomputable section
namespace PfaffianDescent
open Module TrivSqZeroExt
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A] [IsLocalRing A]

private theorem rationalResidue_surjective (rho : A →ₐ[K] K) :
    Function.Surjective rho := by
  intro r
  exact ⟨algebraMap K A r, by simp⟩

/-- A two-dimensional local algebra with rational residue has a nonzero
square-zero generator of its residue kernel. Locality rules out the split
quadratic algebra. -/
theorem lengthTwoLocal_exists_squareZero_generator
    (rho : A →ₐ[K] K) (hA : finrank K A = 2) :
    ∃ t : A, t ≠ 0 ∧ rho t = 0 ∧ t * t = 0 ∧
      ∀ x : A, rho x = 0 → ∃ c : K, c • t = x := by
  let V := LinearMap.ker rho.toLinearMap
  have hV : finrank K V = 1 := by
    have hsum := rho.toLinearMap.finrank_range_add_finrank_ker
    change finrank K (LinearMap.range rho.toLinearMap) + finrank K V =
      finrank K A at hsum
    rw [LinearMap.range_eq_top.mpr (rationalResidue_surjective rho), finrank_top,
      hA] at hsum
    simp only [Module.finrank_self] at hsum
    omega
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; decide)
  obtain ⟨t, ht⟩ := exists_ne (0 : V)
  have htA : (t : A) ≠ 0 := by
    intro hz
    apply ht
    exact Subtype.ext hz
  have hrho : rho (t : A) = 0 := t.property
  let t2 : V := ⟨(t : A) * t, by simp [V, LinearMap.mem_ker, map_mul, hrho]⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hV ht t2
  have hcA : c • (t : A) = (t : A) * t := congrArg Subtype.val hc
  have hc0 : c = 0 := by
    by_contra hcne
    have hunit : IsUnit ((t : A) - algebraMap K A c) := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      rw [← IsLocalRing.ker_eq_maximalIdeal rho.toRingHom
        (rationalResidue_surjective rho)]
      change rho ((t : A) - algebraMap K A c) ≠ 0
      simpa [hrho] using neg_ne_zero.mpr hcne
    have hprod : (t : A) * ((t : A) - algebraMap K A c) = 0 := by
      rw [mul_sub, ← hcA, Algebra.smul_def, mul_comm (t : A)]
      exact sub_self _
    exact htA (hunit.mul_right_cancel (by simpa using hprod))
  have ht2 : (t : A) * t = 0 := by
    simpa [hc0] using hcA.symm
  refine ⟨t, htA, hrho, ht2, ?_⟩
  intro x hx
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hV ht
    (⟨x, hx⟩ : V)
  exact ⟨c, congrArg Subtype.val hc⟩

private def squareZeroScalarMap (t : A) : K →ₗ[K] A where
  toFun c := c • t
  map_add' c d := add_smul c d t
  map_smul' c d := smul_assoc c d t

private def squareZeroDualMap (t : A) (ht : t * t = 0) : DualNumber K →ₐ[K] A :=
  TrivSqZeroExt.liftEquivOfComm ⟨squareZeroScalarMap t, by
    intro c d
    change (c • t) * (d • t) = 0
    simp only [Algebra.smul_def]
    calc
      (algebraMap K A c * t) * (algebraMap K A d * t) =
          (algebraMap K A c * algebraMap K A d) * (t * t) := by ring
      _ = 0 := by rw [ht, mul_zero]⟩

private theorem squareZeroDualMap_apply (t : A) (ht : t * t = 0)
    (z : DualNumber K) :
    squareZeroDualMap t ht z = algebraMap K A z.fst + z.snd • t := rfl

/-- A genuine algebra equivalence with the dual numbers, not a chosen
geometric-jet certificate. It is derived for every local length-two algebra. -/
theorem lengthTwoLocal_dual_equiv_of_rational_residue
    (rho : A →ₐ[K] K) (hA : finrank K A = 2) :
    Nonempty (DualNumber K ≃ₐ[K] A) := by
  obtain ⟨t, ht0, hrho, ht2, hspan⟩ :=
    lengthTwoLocal_exists_squareZero_generator rho hA
  let phi : DualNumber K →ₐ[K] A := squareZeroDualMap (K := K) t ht2
  have hsurj : Function.Surjective phi := by
    intro x
    have hker : rho (x - algebraMap K A (rho x)) = 0 := by simp
    obtain ⟨c, hc⟩ := hspan _ hker
    refine ⟨TrivSqZeroExt.inl (rho x) + TrivSqZeroExt.inr c, ?_⟩
    rw [squareZeroDualMap_apply]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rw [hc]
    ring
  have hdim : finrank K (DualNumber K) = finrank K A := by
    change finrank K (K × K) = finrank K A
    simp [Module.finrank_prod, hA]
  -- The algebra-induced scalar action on DualNumber is not registered as
  -- the product module instance. Its proven positive finrank supplies the
  -- actual finite-dimensional instance needed by the linear-map criterion.
  letI : FiniteDimensional K (DualNumber K) :=
    Module.finite_of_finrank_pos (by rw [hdim, hA]; decide)
  have hinj : Function.Injective phi :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := phi.toLinearMap)).mpr hsurj
  exact ⟨AlgEquiv.ofBijective phi ⟨hinj, hsurj⟩⟩

/-- Over an algebraically closed field the rational-residue map is itself
constructed from the actual maximal-ideal quotient. -/
theorem lengthTwoLocal_dual_equiv [IsAlgClosed K]
    (hA : finrank K A = 2) : Nonempty (DualNumber K ≃ₐ[K] A) := by
  let F := A ⧸ IsLocalRing.maximalIdeal A
  let q := Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal A)
  letI : Module.Finite K F := Module.Finite.of_surjective q.toLinearMap
    (Ideal.Quotient.mkₐ_surjective K (IsLocalRing.maximalIdeal A))
  let e : K ≃ₐ[K] F := AlgEquiv.ofBijective (Algebra.ofId K F)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))
  let rho : A →ₐ[K] K := e.symm.toAlgHom.comp q
  exact lengthTwoLocal_dual_equiv_of_rational_residue rho hA

end PfaffianDescent
