import PfaffianDescent.FrameArtin
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent.FrameArtin
open Module

section
variable {K : Type*} [CommRing K]

/-- Projection to the constant coefficient. -/
def augmentation : FrameArtin K →+* K where
  toFun a := a.coeff 0
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance [Nontrivial K] : Nontrivial (FrameArtin K) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  exact zero_ne_one (congrArg (fun a : FrameArtin K => a.coeff 0) h)

/-- The annihilator of the positive-degree ideal. -/
def socle : Submodule K (FrameArtin K) where
  carrier := {a | ∀ b : FrameArtin K, b.coeff 0 = 0 → a * b = 0}
  zero_mem' := by intro b _; exact zero_mul b
  add_mem' := by intro a b ha hb c hc; rw [add_mul, ha c hc, hb c hc, add_zero]
  smul_mem' := by intro s a ha b hb; rw [smul_mul_assoc, ha b hb, smul_zero]

end

section
variable {K : Type*} [Field K]

instance : FiniteDimensional K (FrameArtin K) := (coeffLinearEquiv (K := K)).symm.finiteDimensional

instance : IsArtinianRing (FrameArtin K) := IsArtinianRing.of_finite K (FrameArtin K)

theorem finrank_eq_five : finrank K (FrameArtin K) = 5 := by
  rw [coeffLinearEquiv.finrank_eq]
  simp

/-- A nonzero constant coefficient makes an element invertible. -/
theorem isUnit_of_constant_ne_zero (a : FrameArtin K) (ha : a.coeff 0 ≠ 0) : IsUnit a := by
  let b : FrameArtin K := ⟨![(a.coeff 0)⁻¹, (-(a.coeff 0)⁻¹^2*a.coeff 1), (-(a.coeff 0)⁻¹^2*a.coeff 2), (-(a.coeff 0)⁻¹^2*a.coeff 3), ((a.coeff 0)⁻¹^3*((-3)*a.coeff 1*a.coeff 1+a.coeff 1*a.coeff 2+a.coeff 1*a.coeff 3+a.coeff 2*a.coeff 1+(-3)*a.coeff 2*a.coeff 2+a.coeff 2*a.coeff 3+a.coeff 3*a.coeff 1+a.coeff 3*a.coeff 2+(-3)*a.coeff 3*a.coeff 3)-(a.coeff 0)⁻¹^2*a.coeff 4)]⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨b, ?_⟩
  apply FrameArtin.ext
  funext i
  fin_cases i
  · change (a.coeff 0*(a.coeff 0)⁻¹) = 1
    field_simp [ha]
  · change (a.coeff 0*(-(a.coeff 0)⁻¹^2*a.coeff 1)+a.coeff 1*(a.coeff 0)⁻¹) = 0
    field_simp [ha]
    ring
  · change (a.coeff 0*(-(a.coeff 0)⁻¹^2*a.coeff 2)+a.coeff 2*(a.coeff 0)⁻¹) = 0
    field_simp [ha]
    ring
  · change (a.coeff 0*(-(a.coeff 0)⁻¹^2*a.coeff 3)+a.coeff 3*(a.coeff 0)⁻¹) = 0
    field_simp [ha]
    ring
  · change (a.coeff 0*((a.coeff 0)⁻¹^3*((-3)*a.coeff 1*a.coeff 1+a.coeff 1*a.coeff 2+a.coeff 1*a.coeff 3+a.coeff 2*a.coeff 1+(-3)*a.coeff 2*a.coeff 2+a.coeff 2*a.coeff 3+a.coeff 3*a.coeff 1+a.coeff 3*a.coeff 2+(-3)*a.coeff 3*a.coeff 3)-(a.coeff 0)⁻¹^2*a.coeff 4)+a.coeff 4*(a.coeff 0)⁻¹+(-3)*a.coeff 1*(-(a.coeff 0)⁻¹^2*a.coeff 1)+a.coeff 1*(-(a.coeff 0)⁻¹^2*a.coeff 2)+a.coeff 1*(-(a.coeff 0)⁻¹^2*a.coeff 3)+a.coeff 2*(-(a.coeff 0)⁻¹^2*a.coeff 1)+(-3)*a.coeff 2*(-(a.coeff 0)⁻¹^2*a.coeff 2)+a.coeff 2*(-(a.coeff 0)⁻¹^2*a.coeff 3)+a.coeff 3*(-(a.coeff 0)⁻¹^2*a.coeff 1)+a.coeff 3*(-(a.coeff 0)⁻¹^2*a.coeff 2)+(-3)*a.coeff 3*(-(a.coeff 0)⁻¹^2*a.coeff 3)) = 0
    field_simp [ha]
    ring

theorem isUnit_iff_constant_ne_zero (a : FrameArtin K) : IsUnit a ↔ a.coeff 0 ≠ 0 := by
  constructor
  · intro ha
    exact (isUnit_iff_ne_zero.mp (ha.map augmentation))
  · exact isUnit_of_constant_ne_zero a

instance : IsLocalRing (FrameArtin K) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases h : a.coeff 0 = 0
  · right
    apply isUnit_of_constant_ne_zero
    change 1 - a.coeff 0 ≠ 0
    rw [h, sub_zero]
    exact one_ne_zero
  · exact Or.inl (isUnit_of_constant_ne_zero a h)

theorem mem_maximalIdeal_iff (a : FrameArtin K) :
    a ∈ IsLocalRing.maximalIdeal (FrameArtin K) ↔ a.coeff 0 = 0 := by
  change (¬ IsUnit a) ↔ a.coeff 0 = 0
  rw [isUnit_iff_constant_ne_zero, not_not]

theorem socle_is_annihilator (a : FrameArtin K) :
    a ∈ socle ↔ ∀ b ∈ IsLocalRing.maximalIdeal (FrameArtin K), a * b = 0 := by
  simp only [mem_maximalIdeal_iff]
  rfl

end

section
variable {K : Type*} [Field K] [CharZero K]

/-- The nondegenerate multiplication matrix leaves only the degree-two socle. -/
theorem mem_socle_iff (a : FrameArtin K) : a ∈ socle ↔
    a.coeff 0 = 0 ∧ a.coeff 1 = 0 ∧ a.coeff 2 = 0 ∧ a.coeff 3 = 0 := by
  constructor
  · intro ha
    have h0 := congrArg (fun v : FrameArtin K => v.coeff 4)
      (ha (⟨![0, 0, 0, 0, 1]⟩ : FrameArtin K) rfl)
    have h1 := congrArg (fun v : FrameArtin K => v.coeff 4)
      (ha (⟨![0, 1, 0, 0, 0]⟩ : FrameArtin K) rfl)
    have h2 := congrArg (fun v : FrameArtin K => v.coeff 4)
      (ha (⟨![0, 0, 1, 0, 0]⟩ : FrameArtin K) rfl)
    have h3 := congrArg (fun v : FrameArtin K => v.coeff 4)
      (ha (⟨![0, 0, 0, 1, 0]⟩ : FrameArtin K) rfl)
    change (a.coeff 0*1+a.coeff 4*0+(-3)*a.coeff 1*0+a.coeff 1*0+a.coeff 1*0+a.coeff 2*0+(-3)*a.coeff 2*0+a.coeff 2*0+a.coeff 3*0+a.coeff 3*0+(-3)*a.coeff 3*0) = 0 at h0
    change (a.coeff 0*0+a.coeff 4*0+(-3)*a.coeff 1*1+a.coeff 1*0+a.coeff 1*0+a.coeff 2*1+(-3)*a.coeff 2*0+a.coeff 2*0+a.coeff 3*1+a.coeff 3*0+(-3)*a.coeff 3*0) = 0 at h1
    change (a.coeff 0*0+a.coeff 4*0+(-3)*a.coeff 1*0+a.coeff 1*1+a.coeff 1*0+a.coeff 2*0+(-3)*a.coeff 2*1+a.coeff 2*0+a.coeff 3*0+a.coeff 3*1+(-3)*a.coeff 3*0) = 0 at h2
    change (a.coeff 0*0+a.coeff 4*0+(-3)*a.coeff 1*0+a.coeff 1*0+a.coeff 1*1+a.coeff 2*0+(-3)*a.coeff 2*0+a.coeff 2*1+a.coeff 3*0+a.coeff 3*0+(-3)*a.coeff 3*1) = 0 at h3
    simp only [mul_zero, mul_one, zero_add, add_zero] at h0 h1 h2 h3
    refine ⟨h0, ?_, ?_, ?_⟩
    · linear_combination -(1/2 : K) * h1 - (1/4 : K) * h2 - (1/4 : K) * h3
    · linear_combination -(1/4 : K) * h1 - (1/2 : K) * h2 - (1/4 : K) * h3
    · linear_combination -(1/4 : K) * h1 - (1/4 : K) * h2 - (1/2 : K) * h3
  · rintro ⟨h0, h1, h2, h3⟩ b hb
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change (a.coeff 0*b.coeff 0) = 0
      simp only [h0, h1, h2, h3, hb, zero_mul, mul_zero, add_zero]
    · change (a.coeff 0*b.coeff 1+a.coeff 1*b.coeff 0) = 0
      simp only [h0, h1, h2, h3, hb, zero_mul, mul_zero, add_zero]
    · change (a.coeff 0*b.coeff 2+a.coeff 2*b.coeff 0) = 0
      simp only [h0, h1, h2, h3, hb, zero_mul, mul_zero, add_zero]
    · change (a.coeff 0*b.coeff 3+a.coeff 3*b.coeff 0) = 0
      simp only [h0, h1, h2, h3, hb, zero_mul, mul_zero, add_zero]
    · change (a.coeff 0*b.coeff 4+a.coeff 4*b.coeff 0+(-3)*a.coeff 1*b.coeff 1+a.coeff 1*b.coeff 2+a.coeff 1*b.coeff 3+a.coeff 2*b.coeff 1+(-3)*a.coeff 2*b.coeff 2+a.coeff 2*b.coeff 3+a.coeff 3*b.coeff 1+a.coeff 3*b.coeff 2+(-3)*a.coeff 3*b.coeff 3) = 0
      simp only [h0, h1, h2, h3, hb, zero_mul, mul_zero, add_zero]

/-- The socle is one-dimensional over the residue field. -/
def socleLinearEquiv : socle (K := K) ≃ₗ[K] K where
  toFun a := a.val.coeff 4
  invFun c := ⟨⟨![0, 0, 0, 0, c]⟩, (mem_socle_iff _).mpr ⟨rfl, rfl, rfl, rfl⟩⟩
  left_inv a := by
    apply Subtype.ext
    apply FrameArtin.ext
    funext i
    obtain ⟨h0, h1, h2, h3⟩ := (mem_socle_iff a.val).mp a.property
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem socle_finrank : finrank K (socle (K := K)) = 1 := by
  rw [socleLinearEquiv.finrank_eq]
  exact Module.finrank_self K

end
end PfaffianDescent.FrameArtin
