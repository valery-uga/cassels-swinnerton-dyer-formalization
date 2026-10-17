import PfaffianDescent.AlternatingCoordinates

namespace PfaffianDescent
section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An alternating bilinear form, regarded as an alternating map on two inputs. -/
def alternatingOfBilinear (B : M →ₗ[R] M →ₗ[R] R) (hB : B.IsAlt) : AlternatingTwoForms R M where
  toFun v := B (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [map_add]
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change v 0 = v 1 at h
      change B (v 0) (v 1) = 0
      rw [h]
      exact hB _
    · change v 1 = v 0 at h
      change B (v 0) (v 1) = 0
      rw [h]
      exact hB _
    · exact (hij rfl).elim

lemma alternatingOfBilinear_pair (B : M →ₗ[R] M →ₗ[R] R) (hB : B.IsAlt) (x y : M) :
    alternatingOfBilinear B hB ![x, y] = B x y := rfl

lemma alternatingBilinear_ofBilinear (B : M →ₗ[R] M →ₗ[R] R) (hB : B.IsAlt) :
    alternatingBilinear (alternatingOfBilinear B hB) = B := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

lemma alternatingOfBilinear_alternatingBilinear (B : AlternatingTwoForms R M) :
    alternatingOfBilinear (alternatingBilinear B) (alternatingBilinear_self B) = B := by
  ext v
  change B ![v 0, v 1] = B v
  congr 1
  funext i
  fin_cases i <;> rfl

end
end PfaffianDescent
