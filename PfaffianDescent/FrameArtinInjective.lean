import PfaffianDescent.FrameArtinSocle
import PfaffianDescent.FrobeniusInjective

namespace PfaffianDescent.FrameArtin
open Module
section
variable {K : Type*} [Field K] [CharZero K]

noncomputable def topCoefficient : Module.Dual K (FrameArtin K) :=
  (LinearMap.proj 4).comp coeffLinearEquiv.toLinearMap

@[simp] lemma topCoefficient_apply (a : FrameArtin K) : topCoefficient a = a.coeff 4 := rfl

/-- The top coefficient gives a nondegenerate multiplication pairing on the
actual five-dimensional Artinian algebra. -/
theorem topCoefficient_frobenius : IsFrobeniusFunctional (topCoefficient (K := K)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have he (b : FrameArtin K) : (a*b).coeff 4 = 0 := LinearMap.congr_fun ha b
  have h0 : a.coeff 0 = 0 := by
    have h := he (⟨![0,0,0,0,1]⟩ : FrameArtin K)
    change a.coeff 0*1+a.coeff 4*0+(-3)*a.coeff 1*0+a.coeff 1*0+a.coeff 1*0+
      a.coeff 2*0+(-3)*a.coeff 2*0+a.coeff 2*0+a.coeff 3*0+a.coeff 3*0+
      (-3)*a.coeff 3*0 = 0 at h
    simpa only [mul_one, mul_zero, add_zero] using h
  have hs : a ∈ socle := by
    intro b hb
    apply FrameArtin.ext
    funext i
    fin_cases i
    · change a.coeff 0 * b.coeff 0 = 0
      rw [h0, zero_mul]
    · change a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0 = 0
      rw [h0, hb, zero_mul, mul_zero, add_zero]
    · change a.coeff 0 * b.coeff 2 + a.coeff 2 * b.coeff 0 = 0
      rw [h0, hb, zero_mul, mul_zero, add_zero]
    · change a.coeff 0 * b.coeff 3 + a.coeff 3 * b.coeff 0 = 0
      rw [h0, hb, zero_mul, mul_zero, add_zero]
    · exact he b
  obtain ⟨_, h1, h2, h3⟩ := (mem_socle_iff a).mp hs
  have h4 : a.coeff 4 = 0 := by simpa only [mul_one] using he 1
  apply FrameArtin.ext
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The Artinian reduction has injective dimension zero as a module over itself,
the Artinian Gorenstein property. -/
theorem self_injective : Module.Injective (FrameArtin K) (FrameArtin K) :=
  injective_of_frobenius topCoefficient topCoefficient_frobenius

end
end PfaffianDescent.FrameArtin
