import PfaffianDescent.CubicEvaluation
import PfaffianDescent.PrimitiveSpan

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- Products of three elements of the coordinate span are cubic evaluations. -/
theorem product_mem_cubicEvaluation_range (p : Vec L n) (x y z : L)
    (hx : x ∈ Submodule.span K (Set.range p))
    (hy : y ∈ Submodule.span K (Set.range p))
    (hz : z ∈ Submodule.span K (Set.range p)) :
    x * y * z ∈ LinearMap.range (cubicEvaluation p : Cubic K n →ₗ[K] L) := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hz
  refine ⟨Cubic.tensor a b d, ?_⟩
  rw [cubicEvaluation_eq]
  have hmap : (Cubic.tensor a b d).map (algebraMap K L) =
      Cubic.tensor (fun i => algebraMap K L (a i)) (fun i => algebraMap K L (b i))
        (fun i => algebraMap K L (d i)) := by
    funext i
    simp only [Cubic.map, Cubic.tensor, map_mul]
  rw [hmap, Cubic.eval_tensor]
  simpa only [Algebra.smul_def] using congrArg (fun t : L × L × L => t.1 * t.2.1 * t.2.2)
    (show (∑ i, a i • p i, ∑ i, b i • p i, ∑ i, d i • p i) = (x, y, z) by rw [ha, hb, hd])

end

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {n : ℕ}

/-- In degree four, a normalized generating tuple has surjective cubic evaluation. -/
theorem quartic_cubicEvaluation_surjective (hdim : finrank K L = 4)
    (p : Vec L n) (k : Fin n) (hk : p k = 1)
    (hgen : IntermediateField.adjoin K (Set.range p) = ⊤) :
    Function.Surjective (cubicEvaluation p : Cubic K n →ₗ[K] L) := by
  obtain ⟨a, ha, hfield⟩ := primitive_in_coordinate_span (K := K) p
  obtain ⟨b, hb⟩ := primitive_power_basis hdim a (hfield.symm.trans hgen)
  have h1 : (1 : L) ∈ Submodule.span K (Set.range p) := by
    rw [← hk]
    exact Submodule.subset_span (Set.mem_range_self k)
  have hpows : ∀ i : Fin 4,
      a^(i : ℕ) ∈ LinearMap.range (cubicEvaluation p : Cubic K n →ₗ[K] L) := by
    intro i
    fin_cases i
    · simpa only [pow_zero, one_mul] using product_mem_cubicEvaluation_range p 1 1 1 h1 h1 h1
    · simpa only [pow_one, mul_one] using product_mem_cubicEvaluation_range p a 1 1 ha h1 h1
    · simpa only [pow_two, mul_one] using product_mem_cubicEvaluation_range p a a 1 ha ha h1
    · change a^3 ∈ LinearMap.range (cubicEvaluation p : Cubic K n →ₗ[K] L)
      have he : a^3 = a * a * a := by ring
      rw [he]
      exact product_mem_cubicEvaluation_range p a a a ha ha ha
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [hb]
  exact hpows i

end
end PfaffianDescent
