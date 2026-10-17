import AllCharacteristics.GradedChartCoordinates
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace PfaffianDescent
open HomogeneousLocalization
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] (z : A)

/-- The ground-field algebra structure on a degree-zero homogeneous chart. -/
@[instance_reducible]
noncomputable def homogeneousChartAlgebra : Algebra K (Away 𝒜 z) :=
  (AllCharacteristics.GradedChart.baseMap 𝒜 (z := z)).toAlgebra

attribute [local instance] homogeneousChartAlgebra

/-- Inclusion of a homogeneous chart into the ordinary localization is ground-field linear. -/
noncomputable def homogeneousChartValLinear :
    Away 𝒜 z →ₗ[K] Localization (Submonoid.powers z) where
  toFun := HomogeneousLocalization.val
  map_add' x y := HomogeneousLocalization.val_add x y
  map_smul' r x := by
    change (algebraMap K (Away 𝒜 z) r * x).val = r • x.val
    rw [HomogeneousLocalization.val_mul, Algebra.smul_def]
    rfl

lemma homogeneousChartValLinear_injective : Function.Injective (homogeneousChartValLinear 𝒜 z) :=
  HomogeneousLocalization.val_injective (Submonoid.powers z)

/-- A finite family of chart elements can be represented by numerators in one
arbitrarily high common degree. -/
theorem homogeneousChart_common_degree {ι : Type*} [Finite ι]
    (hz : z ∈ 𝒜 1) (v : ι → Away 𝒜 z) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ a : ι → 𝒜 n,
      ∀ i, algebraMap A (Localization (Submonoid.powers z)) (a i).val =
        z^n • (v i).val := by
  have hv : ∀ᶠ n in Filter.atTop, ∀ i, z^n • (v i).val ∈
      algebraMap A (Localization (Submonoid.powers z)) '' (𝒜 n : Set A) := by
    apply Filter.eventually_all.mpr
    intro i
    simpa only [smul_eq_mul, mul_one] using Away.eventually_smul_mem hz (v i)
  obtain ⟨n, hn, hav⟩ := (Filter.eventually_ge_atTop N).and hv |>.exists
  choose a ha he using hav
  exact ⟨n, hn, fun i => ⟨a i, ha i⟩, he⟩

end
end PfaffianDescent
