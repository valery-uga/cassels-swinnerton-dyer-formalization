import PfaffianDescent.QuinticAlgebraResolution
import PfaffianDescent.AlgebraVectorIdeal

namespace PfaffianDescent
open MvPolynomial Module
section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]

/-- The canonical power-basis free resolution, with its final image identified
as the homogeneous ideal of the algebra-valued vector itself. -/
theorem quintic_algebra_coordinate_free_resolution (z : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = z^(i : ℕ)) (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) :
    ∃ r : Vec K 5, quinticRelation (fun i => algebraMap K A (r i)) z ∧
      Function.Injective (quinticFirstMap r) ∧
      LinearMap.range (quinticFirstMap r) = LinearMap.ker (quinticMiddleMap r) ∧
      LinearMap.range (quinticMiddleMap r) = LinearMap.ker (quinticLastMap r) ∧
      LinearMap.range (quinticLastMap r) = algebraVectorIdeal (K := K) (rationalCubicCoordinates z) := by
  haveI : FiniteDimensional K A := b.finiteDimensional_of_finite
  have hdim : finrank K A = 5 := by
    rw [finrank_eq_card_basis b, Fintype.card_fin]
  obtain ⟨r, hr, hi, he1, he2, hlast⟩ := quintic_algebra_power_free_resolution z b hb ev hev
  have hcoord : (fun i j => ev i (rationalCubicCoordinates z j)) =
      (fun i => rationalCubicCoordinates (ev i z)) := by
    funext i j
    fin_cases j <;> simp [rationalCubicCoordinates]
  have hI := algebraVectorIdeal_eq_geometric_contract hdim ev hev (rationalCubicCoordinates z)
  rw [hcoord] at hI
  exact ⟨r, hr, hi, he1, he2, hlast.trans hI.symm⟩

end
end PfaffianDescent
