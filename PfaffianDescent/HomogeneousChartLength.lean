import PfaffianDescent.HomogeneousGradeStabilization

namespace PfaffianDescent
open HomogeneousLocalization Module
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] {z : A} (hz : z ∈ 𝒜 1)
attribute [local instance] homogeneousChartAlgebra

lemma homogeneous_power_mul_eq_zero (N : ℕ)
    (hinj : ∀ n, N ≤ n → Function.Injective (homogeneousGradeMul 𝒜 hz n))
    (n : ℕ) (hn : N ≤ n) (m : ℕ) (a : A) (ha : a ∈ 𝒜 n)
    (he : a * z^m = 0) : a = 0 := by
  induction m generalizing n a with
  | zero => simpa using he
  | succ m ih =>
    have ham : a * z ∈ 𝒜 (n+1) := SetLike.mul_mem_graded ha hz
    have he' : (a*z) * z^m = 0 := by
      rw [mul_assoc, ← pow_succ']
      exact he
    have haz : a*z = 0 := ih (n+1) (by omega) (a*z) ham he'
    have hh : homogeneousGradeMul 𝒜 hz n ⟨a, ha⟩ =
        homogeneousGradeMul 𝒜 hz n 0 := Subtype.ext (by simpa [homogeneousGradeMul] using haz)
    exact congrArg Subtype.val (hinj n hn hh)

/-- Above stabilization, localization does not kill any homogeneous element. -/
theorem homogeneousGrade_localization_injective (N : ℕ)
    (hinj : ∀ n, N ≤ n → Function.Injective (homogeneousGradeMul 𝒜 hz n))
    (n : ℕ) (hn : N ≤ n) :
    Function.Injective ((IsScalarTower.toAlgHom K A (Localization (Submonoid.powers z))).toLinearMap.comp
      (𝒜 n).subtype) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  change algebraMap A (Localization (Submonoid.powers z)) a.val = 0 at ha
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers z) _ a.val).mp ha
  apply Subtype.ext
  exact homogeneous_power_mul_eq_zero 𝒜 hz N hinj n hn m a.val a.2 (by simpa [mul_comm] using hm)

/-- The degree-zero localization has precisely the stable Hilbert dimension
when multiplication by its denominator is eventually injective. -/
theorem homogeneousChart_finrank_of_stable
    [∀ n, Module.Finite K (𝒜 n)] (N D : ℕ)
    (hdim : ∀ n, N ≤ n → finrank K (𝒜 n) = D)
    (hinj : ∀ n, N ≤ n → Function.Injective (homogeneousGradeMul 𝒜 hz n)) :
    finrank K (Away 𝒜 z) = D := by
  obtain ⟨hfin, hle⟩ := homogeneousChart_finite_of_bounded 𝒜 z hz N D
    (fun n hn => (hdim n hn).le)
  have := hfin
  apply le_antisymm hle
  let b := Module.finBasis K (𝒜 N)
  let v (i : Fin (finrank K (𝒜 N))) : Away 𝒜 z :=
    Away.mk 𝒜 hz N (b i).val (by simpa only [smul_eq_mul, mul_one] using (b i).2)
  let L := Localization (Submonoid.powers z)
  let G : 𝒜 N →ₗ[K] L := (IsScalarTower.toAlgHom K A L).toLinearMap.comp (𝒜 N).subtype
  let F : Away 𝒜 z →ₗ[K] L :=
    (LinearMap.mulLeft K (algebraMap A L (z^N))).comp (homogeneousChartValLinear 𝒜 z)
  have he : F ∘ v = G ∘ b := by
    funext i
    change algebraMap A L (z^N) * (v i).val = algebraMap A L (b i).val
    rw [← Algebra.smul_def]
    change z^N • (Away.mk 𝒜 hz N (b i).val _).val = _
    rw [Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.smul_mk'_self (M := Submonoid.powers z) (S := L) (m := ⟨z^N, ⟨N, rfl⟩⟩) (r := (b i).val)
  have hv : LinearIndependent K v := LinearIndependent.of_comp F (by
    rw [he]
    exact b.linearIndependent.map' G (LinearMap.ker_eq_bot.mpr
      (homogeneousGrade_localization_injective 𝒜 hz N hinj N le_rfl)))
  have hc := hv.fintype_card_le_finrank
  simpa only [Fintype.card_fin, hdim N le_rfl] using hc

end
end PfaffianDescent
