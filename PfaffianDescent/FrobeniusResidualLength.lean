import PfaffianDescent.AlgebraFrobenius
import PfaffianDescent.ResidualAlgebraLength

/-!
# Residual length in a finite Frobenius algebra

The zero-dimensional complete intersections occurring in Voisin's residual
constructions are Gorenstein.  Algebraically, a nondegenerate multiplication
functional identifies the quotient by the annihilator of an ideal with the
dual of that ideal.  This file proves the resulting complementary-length
formula in a reusable finite-dimensional form.
-/

namespace PfaffianDescent
open Module

section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A]

/-- The multiplication pairing restricted in its second variable to an
ideal. -/
def frobeniusIdealPairing (ell : Module.Dual K A) (P : Ideal A) :
    A →ₗ[K] Module.Dual K (P.restrictScalars K) where
  toFun a :=
    { toFun := fun b ↦ ell (a * b.val)
      map_add' := by
        intro x y
        rw [Submodule.coe_add, mul_add, map_add]
      map_smul' := by
        intro r x
        change ell (a * (r • x.val)) = r • ell (a * x.val)
        rw [mul_smul_comm, map_smul] }
  map_add' := by
    intro a b
    ext x
    change ell ((a + b) * x.val) = ell (a * x.val) + ell (b * x.val)
    rw [add_mul, map_add]
  map_smul' := by
    intro r a
    ext x
    change ell ((r • a) * x.val) = r • ell (a * x.val)
    rw [smul_mul_assoc, map_smul]

/-- Restriction of a nondegenerate multiplication pairing to an ideal is
surjective onto the ideal's linear dual. -/
theorem frobeniusIdealPairing_surjective
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) (P : Ideal A) :
    Function.Surjective (frobeniusIdealPairing ell P) := by
  intro psi
  obtain ⟨phi, hphi⟩ := psi.exists_extend
  obtain ⟨a, ha⟩ := frobeniusFunctional_surjective ell hell phi
  refine ⟨a, ?_⟩
  ext b
  change ell (a * b.val) = psi b
  change (algebraMultiplicationDual ell a) b.val = psi b
  rw [LinearMap.congr_fun ha b.val]
  exact LinearMap.congr_fun hphi b

/-- The kernel of the restricted multiplication pairing is exactly the
annihilator ideal, viewed as a `K`-subspace. -/
theorem frobeniusIdealPairing_ker
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) (P : Ideal A) :
    LinearMap.ker (frobeniusIdealPairing ell P) =
      (residualAlgebraIdeal P).restrictScalars K := by
  ext a
  constructor
  · intro ha
    rw [LinearMap.mem_ker] at ha
    rw [Submodule.restrictScalars_mem]
    rw [Module.mem_annihilator]
    intro b
    apply Subtype.ext
    change a * b.val = 0
    apply hell
    apply LinearMap.ext
    intro x
    change ell ((a * b.val) * x) = ell (0 * x)
    have hbx : b.val * x ∈ P := P.mul_mem_right x b.property
    have hz := LinearMap.congr_fun ha ⟨b.val * x, hbx⟩
    change ell (a * (b.val * x)) =
      (0 : Module.Dual K (P.restrictScalars K)) ⟨b.val * x, hbx⟩ at hz
    simpa only [LinearMap.zero_apply, zero_mul, map_zero, mul_assoc] using hz
  · intro ha
    rw [Submodule.restrictScalars_mem, Module.mem_annihilator] at ha
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro b
    change ell (a * b.val) = 0
    have hab : a * b.val = 0 := congrArg Subtype.val (ha ⟨b.val, b.property⟩)
    rw [hab, map_zero]

/-- A Frobenius functional identifies the coordinate algebra of the
annihilator residual with the linear dual of the original ideal.  This is
the local duality behind the complementary residual construction; the
formula on quotient representatives is the restricted multiplication
pairing. -/
noncomputable def residualQuotientLinearEquivIdealDual
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) (P : Ideal A) :
    (A ⧸ residualAlgebraIdeal P) ≃ₗ[K] Module.Dual K (P.restrictScalars K) := by
  let e₁ := (Submodule.Quotient.restrictScalarsEquiv K
    ((residualAlgebraIdeal P : Ideal A) : Submodule A A)).symm
  let e₂ := Submodule.quotEquivOfEq
    ((residualAlgebraIdeal P).restrictScalars K)
    (LinearMap.ker (frobeniusIdealPairing ell P))
    (frobeniusIdealPairing_ker ell hell P).symm
  exact e₁.trans (e₂.trans (LinearMap.quotKerEquivOfSurjective _
    (frobeniusIdealPairing_surjective ell hell P)))

/-- On a quotient representative, residual duality is evaluation by the
Frobenius multiplication pairing. -/
theorem residualQuotientLinearEquivIdealDual_mk
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) (P : Ideal A)
    (a : A) :
    residualQuotientLinearEquivIdealDual ell hell P
        (Ideal.Quotient.mk (residualAlgebraIdeal P) a) =
      frobeniusIdealPairing ell P a := by
  rfl

/-- In a finite Frobenius algebra, the residual quotient by `Ann(P)` has the
same vector-space dimension as `P`. -/
theorem residual_quotient_finrank_eq_ideal
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) (P : Ideal A) :
    finrank K (A ⧸ residualAlgebraIdeal P) = finrank K P := by
  rw [(residualQuotientLinearEquivIdealDual ell hell P).finrank_eq]
  rw [Subspace.dual_finrank_eq]
  rfl

/-- Complementary length for a residual in a finite Frobenius algebra. -/
theorem residual_quotient_finrank_complement
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) (P : Ideal A)
    (N d : ℕ) (hA : finrank K A = N) (hZ : finrank K (A ⧸ P) = d) :
    finrank K (A ⧸ residualAlgebraIdeal P) = N - d := by
  have hPfinite : Module.Finite K P := Module.Finite.of_injective
    (P.restrictScalars K).subtype (Submodule.injective_subtype _)
  have hdim := (P.restrictScalars K).finrank_quotient_add_finrank
  change finrank K (A ⧸ P) + finrank K P = finrank K A at hdim
  rw [residual_quotient_finrank_eq_ideal ell hell P]
  rw [hZ, hA] at hdim
  omega

end
end PfaffianDescent
