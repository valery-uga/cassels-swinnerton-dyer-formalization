import AllCharacteristics.HomogeneousProjective

/-!
# The base ring of a positive-degree projective hypersurface

A positive-degree homogeneous equation has zero constant term. Consequently
its homogeneous quotient retains the coefficient ring exactly in degree zero.
-/

namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
variable (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (hd : 0 < d)
attribute [local instance] MvPolynomial.gradedAlgebra
include hp hd

/-- A homogeneous equation of positive degree has zero constant term. -/
theorem constantCoeff_eq_zero_of_positiveDegree : MvPolynomial.constantCoeff p = 0 := by
  apply hp.coeff_eq_zero
  simpa using (ne_of_lt hd)

/-- The ideal of a positive-degree homogeneous equation is killed by the
constant-coefficient map. -/
theorem equationIdeal_le_ker_constantCoeff :
    (equationIdeal p hp).toIdeal ≤ RingHom.ker (MvPolynomial.constantCoeff :
      MvPolynomial σ R →+* R) := by
  apply Ideal.span_le.mpr
  intro q hq
  have heq : q = p := Set.mem_singleton_iff.mp hq
  subst q
  exact constantCoeff_eq_zero_of_positiveDegree p hp hd

/-- Passing to the homogeneous coordinate ring of a positive-degree equation
does not identify distinct base coefficients. -/
theorem algebraMap_coordinateRing_injective :
    Function.Injective (algebraMap R (CoordinateRing (equationIdeal p hp))) := by
  let e : CoordinateRing (equationIdeal p hp) →+* R :=
    Ideal.Quotient.lift (equationIdeal p hp).toIdeal MvPolynomial.constantCoeff
      (fun a ha ↦ equationIdeal_le_ker_constantCoeff p hp hd ha)
  have he : Function.LeftInverse e (algebraMap R (CoordinateRing (equationIdeal p hp))) := by
    intro r
    change e (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (MvPolynomial.C r)) = r
    exact MvPolynomial.constantCoeff_C σ r
  exact he.injective

/-- The coefficient ring is exactly the degree-zero part of the coordinate
ring of a positive-degree homogeneous hypersurface. -/
theorem algebraMap_gradeZero_bijective :
    Function.Bijective (algebraMap R (grading (equationIdeal p hp) 0)) := by
  refine ⟨?_, algebraMap_gradeZero_surjective (equationIdeal p hp)⟩
  intro r s h
  apply algebraMap_coordinateRing_injective p hp hd
  exact congrArg Subtype.val h

/-- The explicit ring isomorphism between the base ring and the degree-zero
part of a positive-degree homogeneous quotient. -/
noncomputable def gradeZeroEquiv : R ≃+* grading (equationIdeal p hp) 0 :=
  RingEquiv.ofBijective (algebraMap R (grading (equationIdeal p hp) 0))
    (algebraMap_gradeZero_bijective p hp hd)

end HomogeneousProjective
end AllCharacteristics
