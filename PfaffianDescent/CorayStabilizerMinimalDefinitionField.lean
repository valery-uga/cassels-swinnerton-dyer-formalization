import PfaffianDescent.CorayStabilizerHomogeneousIdealDescent

/-! Actual minimality among fields defining the WHOLE homogeneous ideal.
Stability under the fixing subgroup is derived from literal coefficient
extension, rather than supplied. Source only / unverified. -/
noncomputable section
namespace PfaffianDescent.Coray
open scoped Pointwise
universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] polynomialGaloisCoefficientAction

/-- The constructed stabilizer fixed field lies in every intermediate field
whose actual homogeneous ideal extends to C. Combined with checked whole-
ideal descent, this proves minimality for literal homogeneous ideals. -/
theorem homogeneousIdeal_stabilizerFixedField_le_definitionField
    [FiniteDimensional K E] [IsGalois K E]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) E))
    (M : IntermediateField K E)
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hD : D.toIdeal.map (MvPolynomial.map (algebraMap M E)) = C.toIdeal) :
    homogeneousIdealStabilizerFixedField (K := K) C ≤ M := by
  have hsub : M.fixingSubgroup ≤ homogeneousIdealCoefficientStabilizer (K := K) C := by
    intro g hg
    apply MulAction.mem_stabilizer_iff.mpr
    change C.toIdeal.map (MvPolynomial.map g.toRingHom) = C.toIdeal
    rw [← hD, Ideal.map_map]
    have hcomp : (MvPolynomial.map (σ := Fin 4) g.toRingHom).comp
        (MvPolynomial.map (algebraMap M E)) = MvPolynomial.map (algebraMap M E) := by
      apply RingHom.ext
      intro q
      apply MvPolynomial.ext
      intro d
      simp only [RingHom.comp_apply, MvPolynomial.coeff_map]
      exact (IntermediateField.mem_fixingSubgroup_iff M g).mp hg
        (algebraMap M E (MvPolynomial.coeff d q)) (MvPolynomial.coeff d q).2
    rw [hcomp]
  have hle := IntermediateField.fixedField_le hsub
  rw [IsGalois.fixedField_fixingSubgroup M] at hle
  exact hle

end PfaffianDescent.Coray
