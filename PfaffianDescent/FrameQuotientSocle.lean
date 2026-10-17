import PfaffianDescent.FrameQuotientModel

namespace PfaffianDescent.FrameQuotient
open Module

section
variable {K : Type*} [Field K] [CharZero K]

instance : Nontrivial (FrameQuotient K) := by
  refine ⟨⟨algebraEquiv.symm 0, algebraEquiv.symm 1, ?_⟩⟩
  intro h
  exact zero_ne_one (algebraEquiv.symm.injective h)

instance : IsLocalRing (FrameQuotient K) :=
  IsLocalRing.of_surjective' algebraEquiv.symm.toRingHom algebraEquiv.symm.surjective

instance : IsArtinianRing (FrameQuotient K) :=
  IsArtinianRing.of_finite K (FrameQuotient K)

/-- The maximal ideal in the polynomial quotient corresponds to zero constant coefficient. -/
theorem mem_maximalIdeal_iff (a : FrameQuotient K) :
    a ∈ IsLocalRing.maximalIdeal (FrameQuotient K) ↔ (algebraEquiv a).coeff 0 = 0 := by
  change (¬ IsUnit a) ↔ _
  rw [← isUnit_map_iff algebraEquiv a, FrameArtin.isUnit_iff_constant_ne_zero, not_not]

/-- The socle, transported through the proved algebra isomorphism. -/
noncomputable def socle : Submodule K (FrameQuotient K) :=
  FrameArtin.socle.comap algebraEquiv.toLinearMap

theorem socle_is_annihilator (a : FrameQuotient K) :
    a ∈ socle ↔ ∀ b ∈ IsLocalRing.maximalIdeal (FrameQuotient K), a * b = 0 := by
  change (∀ b : FrameArtin K, b.coeff 0 = 0 → algebraEquiv a * b = 0) ↔ _
  constructor
  · intro ha b hb
    apply algebraEquiv.injective
    rw [map_mul, map_zero]
    exact ha (algebraEquiv b) ((mem_maximalIdeal_iff b).mp hb)
  · intro ha b hb
    have hm : algebraEquiv.symm b ∈ IsLocalRing.maximalIdeal (FrameQuotient K) := by
      rw [mem_maximalIdeal_iff, AlgEquiv.apply_symm_apply]
      exact hb
    have he := congrArg algebraEquiv (ha (algebraEquiv.symm b) hm)
    simpa only [map_mul, map_zero, AlgEquiv.apply_symm_apply] using he

noncomputable def socleModelEquiv : socle (K := K) ≃ₗ[K] FrameArtin.socle (K := K) where
  toFun a := ⟨algebraEquiv a, a.property⟩
  invFun a := ⟨algebraEquiv.symm a, by
    change algebraEquiv (algebraEquiv.symm a.val) ∈ FrameArtin.socle
    rw [AlgEquiv.apply_symm_apply]
    exact a.property⟩
  left_inv a := Subtype.ext (AlgEquiv.symm_apply_apply _ _)
  right_inv a := Subtype.ext (AlgEquiv.apply_symm_apply _ _)
  map_add' a b := Subtype.ext (map_add algebraEquiv a.val b.val)
  map_smul' c a := Subtype.ext (map_smul algebraEquiv c a.val)

/-- The actual Artinian quotient has a one-dimensional socle. -/
theorem socle_finrank : finrank K (socle (K := K)) = 1 := by
  rw [socleModelEquiv.finrank_eq, FrameArtin.socle_finrank]

end
end PfaffianDescent.FrameQuotient
