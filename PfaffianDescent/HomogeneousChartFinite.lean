import PfaffianDescent.HomogeneousChartLinear
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace PfaffianDescent
open HomogeneousLocalization Module
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] (z : A)
attribute [local instance] homogeneousChartAlgebra

/-- Bounded homogeneous dimensions bound the size of every independent family
in an actual degree-zero localization chart. -/
theorem homogeneousChart_independent_card_le
    (hz : z ∈ 𝒜 1) (N D : ℕ) [∀ n, Module.Finite K (𝒜 n)]
    (hD : ∀ n, N ≤ n → finrank K (𝒜 n) ≤ D)
    {ι : Type*} [Fintype ι] (v : ι → Away 𝒜 z) (hv : LinearIndependent K v) :
    Fintype.card ι ≤ D := by
  obtain ⟨n, hn, a, ha⟩ := homogeneousChart_common_degree 𝒜 z hz v N
  let L := Localization (Submonoid.powers z)
  have hu : IsUnit (algebraMap A L (z^n)) :=
    IsLocalization.map_units (M := Submonoid.powers z) L ⟨z^n, ⟨n, rfl⟩⟩
  let F : Away 𝒜 z →ₗ[K] L :=
    (LinearMap.mulLeft K (algebraMap A L (z^n))).comp (homogeneousChartValLinear 𝒜 z)
  have hF : Function.Injective F := hu.mul_right_injective.comp
    (homogeneousChartValLinear_injective 𝒜 z)
  let G : 𝒜 n →ₗ[K] L :=
    (IsScalarTower.toAlgHom K A L).toLinearMap.comp (𝒜 n).subtype
  have he : G ∘ a = F ∘ v := by
    funext i
    change algebraMap A L (a i).val = algebraMap A L (z^n) * (v i).val
    rw [← Algebra.smul_def]
    exact ha i
  have haI : LinearIndependent K a := LinearIndependent.of_comp G (by
    rw [he]
    exact hv.map' F (LinearMap.ker_eq_bot.mpr hF))
  exact haI.fintype_card_le_finrank.trans (hD n hn)

/-- Eventual boundedness of the homogeneous Hilbert function implies that every
standard homogeneous chart is finite-dimensional over the coefficient field. -/
theorem homogeneousChart_finite_of_bounded
    (hz : z ∈ 𝒜 1) (N D : ℕ) [∀ n, Module.Finite K (𝒜 n)]
    (hD : ∀ n, N ≤ n → finrank K (𝒜 n) ≤ D) :
    Module.Finite K (Away 𝒜 z) ∧ finrank K (Away 𝒜 z) ≤ D := by
  have hr : Module.rank K (Away 𝒜 z) ≤ D := by
    by_contra h
    have hlt : (D : Cardinal) < Module.rank K (Away 𝒜 z) := lt_of_not_ge h
    have hle : ((D+1 : ℕ) : Cardinal) ≤ Module.rank K (Away 𝒜 z) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hlt
    obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hle
    have hc := homogeneousChart_independent_card_le 𝒜 z hz N D hD v hv
    simp only [Fintype.card_fin] at hc
    omega
  exact ⟨Module.rank_lt_aleph0_iff.mp (hr.trans_lt Cardinal.natCast_lt_aleph0),
    Module.finrank_le_of_rank_le hr⟩

end
end PfaffianDescent
