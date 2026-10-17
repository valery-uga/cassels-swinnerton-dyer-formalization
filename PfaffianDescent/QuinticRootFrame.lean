import PfaffianDescent.QuinticResolutionDescent
import PfaffianDescent.CubicRemainder
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Nonsingular

namespace PfaffianDescent
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
section
variable {K : Type*} [Field K]

/-- Five distinct parameters on the rational normal cubic form a projective frame. -/
theorem rationalCubicCoordinates_general_position (z : Fin 5 → K) (hz : Function.Injective z) :
    FivePointGeneralPosition (fun i => rationalCubicCoordinates (z i)) := by
  intro f hf
  have he : (fun i : Fin 4 => rationalCubicCoordinates (z (f i))) =
      Matrix.vandermonde (fun i : Fin 4 => z (f i)) := by
    funext i j
    fin_cases j <;> simp [rationalCubicCoordinates, Matrix.vandermonde]
  change LinearIndependent K (fun i : Fin 4 => rationalCubicCoordinates (z (f i)))
  rw [he]
  exact (Matrix.nonsingular_iff_det_ne_zero.mpr
    (Matrix.det_vandermonde_ne_zero_iff.mpr (hz.comp hf))).linearIndependent_row

end
section
variable {R : Type*} [CommRing R]

lemma quinticQuadrics_smul (a : Vec R 5) (x : Vec R 4) (t : R) :
    quinticQuadrics a (t • x) = t^2 • quinticQuadrics a x := by
  funext i
  fin_cases i <;> simp [quinticQuadrics, Pi.smul_apply, smul_eq_mul] <;> ring

end
section
variable {K : Type*} [Field K]

/-- A zero of the five homogeneous quadrics gives containment in the actual
homogeneous ideal of its projective point. -/
theorem quinticRelations_mem_point (a : Vec K 5) (x : Vec K 4)
    (hx : quinticQuadrics a x = 0) (i : Fin 5) :
    quinticRelations a i ∈ (vectorLineIdeal x).toIdeal := by
  change vectorLineHom x (quinticRelations a i) = 0
  have ha : ((vectorLineHom x).toRingHom ∘ (fun j : Fin 5 => C (a j))) =
      (fun j : Fin 5 => C (a j) : Fin 5 → MvPolynomial Unit K) := by
    funext j
    change vectorLineHom x (C (a j)) = C (a j)
    simp [vectorLineHom]
  have hX : ((vectorLineHom x).toRingHom ∘ (X : Fin 4 → MvPolynomial (Fin 4) K)) =
      (X () : MvPolynomial Unit K) • (fun j => C (x j)) := by
    funext j
    change vectorLineHom x (X j) = X () * C (x j)
    rw [vectorLineHom_X, mul_comm]
  change (vectorLineHom x).toRingHom (quinticQuadrics (fun j => C (a j)) X i) = 0
  rw [quinticQuadrics_map, ha, hX, quinticQuadrics_smul]
  change X ()^2 * quinticQuadrics (C ∘ a) (C ∘ x) i = 0
  rw [← quinticQuadrics_map, hx, Pi.zero_apply, map_zero, mul_zero]

/-- A monic quintic with five distinct roots has the displayed projective-frame
ideal and hence the full explicit free resolution. -/
theorem quintic_roots_free_resolution (a : Vec K 5) (z : Fin 5 → K)
    (hz : Function.Injective z) (hroot : ∀ j, quinticRelation a (z j)) :
    Function.Injective (quinticFirstMap a) ∧
    LinearMap.range (quinticFirstMap a) = LinearMap.ker (quinticMiddleMap a) ∧
    LinearMap.range (quinticMiddleMap a) = LinearMap.ker (quinticLastMap a) ∧
    LinearMap.range (quinticLastMap a) = fiveVectorIdeal (fun j => rationalCubicCoordinates (z j)) := by
  apply quintic_frame_free_resolution a _ (rationalCubicCoordinates_general_position z hz)
  intro i
  rw [fiveVectorIdeal, Submodule.mem_iInf]
  intro j
  exact quinticRelations_mem_point a _ (quinticQuadrics_at_root a (z j) (hroot j)) i

end
end PfaffianDescent
