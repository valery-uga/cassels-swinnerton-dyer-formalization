import PfaffianDescent.QuinticFrobenius
import PfaffianDescent.CubicCoordinates
import Mathlib.LinearAlgebra.Matrix.Nonsingular

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The first four powers are exactly the kernel of the top-coefficient functional. -/
theorem quintic_power_span_eq_kernel (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) :
    Submodule.span K (Set.range (fun i : Fin 4 => a^(i : ℕ))) =
      LinearMap.ker (quinticPowerFunctional b) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change quinticPowerFunctional b (a^(i : ℕ)) = 0
    have h := quinticPowerFunctional_pow a b hb i.castSucc
    have hi : i.castSucc ≠ (4 : Fin 5) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = 4 at hv
      omega
    simpa only [Fin.val_castSucc, hi, ↓reduceIte] using h
  · intro v hv
    have htop : b.repr v 4 = 0 := hv
    have hmem (i : Fin 4) : a^(i : ℕ) ∈
        Submodule.span K (Set.range (fun i : Fin 4 => a^(i : ℕ))) :=
      Submodule.subset_span (Set.mem_range_self i)
    have h0 : (1 : A) ∈ Submodule.span K (Set.range (fun i : Fin 4 => a^(i : ℕ))) := by
      simpa using hmem 0
    have h1 : a ∈ Submodule.span K (Set.range (fun i : Fin 4 => a^(i : ℕ))) := by
      simpa using hmem 1
    have h2 : a^2 ∈ Submodule.span K (Set.range (fun i : Fin 4 => a^(i : ℕ))) := by
      simpa using hmem 2
    have h3 : a^3 ∈ Submodule.span K (Set.range (fun i : Fin 4 => a^(i : ℕ))) := by
      simpa using hmem 3
    rw [quintic_power_repr_expansion a b hb v]
    rw [htop, zero_smul, add_zero]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1))
        (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3)

/-- A hyperplane with nondegenerate multiplication pairing is a unit translate of
power-basis coordinates in a quintic algebra. -/
theorem quintic_algebra_hyperplane_normal_form (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell) :
    ∃ u : Aˣ, Submodule.span K (Set.range (fun i : Fin 4 => u.val * a^(i : ℕ))) =
      LinearMap.ker ell := by
  letI : FiniteDimensional K A := b.finiteDimensional_of_finite
  obtain ⟨u, hu⟩ := frobenius_functionals_multiplicative ell (quinticPowerFunctional b)
    hell (quinticPowerFunctional_frobenius a b hb)
  refine ⟨u, ?_⟩
  have hmap : Submodule.span K (Set.range (fun i : Fin 4 => u.val * a^(i : ℕ))) =
      (Submodule.span K (Set.range (fun i : Fin 4 => a^(i : ℕ)))).map (LinearMap.mulLeft K u.val) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hmap, quintic_power_span_eq_kernel a b hb]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change ell (u.val*w) = 0
    rw [hu]
    exact hw
  · intro hv
    change ell v = 0 at hv
    refine ⟨(↑u⁻¹ : A) * v, ?_, ?_⟩
    · change quinticPowerFunctional b ((↑u⁻¹ : A)*v) = 0
      rw [← hu, ← mul_assoc, Units.mul_inv]
      simpa only [one_mul] using hv
    · change u.val * ((↑u⁻¹ : A)*v) = v
      rw [← mul_assoc, Units.mul_inv, one_mul]

/-- Independent coordinates in a Frobenius hyperplane are an invertible ground-field
linear change of the four powers, up to one common algebra unit. -/
theorem independent_quintic_algebra_coordinates (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (p : Vec A 4) (hp : LinearIndependent K p)
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell)
    (hspan : Submodule.span K (Set.range p) = LinearMap.ker ell) :
    ∃ u : Aˣ, ∃ M : Mat K 4, Function.Injective M.mulVec ∧
      p = u.val • (M.map (algebraMap K A)).mulVec (rationalCubicCoordinates a) := by
  obtain ⟨u, hu⟩ := quintic_algebra_hyperplane_normal_form a b hb ell hell
  have hmem : ∀ i, p i ∈ Submodule.span K (Set.range (fun j : Fin 4 => u.val * a^(j : ℕ))) := by
    intro i
    rw [hu, ← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (hmem i)
  let phi : Vec K 4 →ₗ[K] A :=
    { toFun := fun d => ∑ j : Fin 4, d j • (u.val * a^(j : ℕ))
      map_add' := by intro x y; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro s x; simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hcomp : phi ∘ M = p := funext hM
  have hrows : LinearIndependent K M := LinearIndependent.of_comp phi (by rw [hcomp]; exact hp)
  have hinj : Function.Injective (Matrix.mulVec (M : Mat K 4)) :=
    Matrix.mulVec_injective_iff.mpr (Matrix.Nonsingular.of_linearIndependent_row hrows).linearIndependent_col
  refine ⟨u, M, hinj, ?_⟩
  have hpow : ∀ j : Fin 4, rationalCubicCoordinates a j = a^(j : ℕ) := by
    intro j
    fin_cases j
    · exact (pow_zero a).symm
    · exact (pow_one a).symm
    · rfl
    · rfl
  funext i
  rw [← hM i]
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, smul_eq_mul,
    hpow, Finset.mul_sum, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  change algebraMap K A (M i j) * (u.val * a^(j : ℕ)) = u.val * (algebraMap K A (M i j) * a^(j : ℕ))
  ring

end
end PfaffianDescent
