import PfaffianDescent.HomogeneousCoordinatesBaseChange
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import PfaffianDescent.HomogeneousDimensions

/-!
# Base change of a homogeneous frame

Homogeneous polynomial spaces have finite monomial coordinates. Linear
independence of a ground-field frame therefore survives any field extension.
A full ground-field basis remains a full basis after that extension.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneousFrame_baseChange_linearIndependent
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {d m n : ℕ} (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame) :
    LinearIndependent L
      (fun i => homogeneousSubmoduleBaseChange (σ := Fin 4) d
        (algebraMap K L) (frame i)) := by
  let EK := homogeneousCoefficientLinearEquivOverRing (R := K) (σ := Fin 4) d e
  let EL := homogeneousCoefficientLinearEquivOverRing (R := L) (σ := Fin 4) d e
  have hK : LinearIndependent K (fun i => EK (frame i)) :=
    hframe.map' EK.toLinearMap (LinearMap.ker_eq_bot.mpr EK.injective)
  have hL : LinearIndependent L
      (fun i => fun j => algebraMap K L (EK (frame i) j)) :=
    (linearIndependent_algebraMap_comp_iff).mpr hK
  have heq : (fun i => EL (homogeneousSubmoduleBaseChange (σ := Fin 4) d
      (algebraMap K L) (frame i))) =
      (fun i => fun j => algebraMap K L (EK (frame i) j)) := by
    funext i j
    exact congrFun (homogeneousCoefficientMapOverRing_baseChange
      (R := K) (S := L) (σ := Fin 4) d (algebraMap K L) e (frame i)) j
  rw [← heq] at hL
  exact hL.of_comp EL.toLinearMap

theorem homogeneousFrame_baseChange_span_top
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {d m : ℕ} (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Basis (Fin (Module.finrank K
      (homogeneousSubmodule (Fin 4) K d))) K
      (homogeneousSubmodule (Fin 4) K d)) :
    Submodule.span L (Set.range
      (fun i => homogeneousSubmoduleBaseChange (σ := Fin 4) d
        (algebraMap K L) (frame i))) = ⊤ := by
  have hLI := homogeneousFrame_baseChange_linearIndependent
    (K := K) (L := L) e frame frame.linearIndependent
  have hcard : Fintype.card (Fin (Module.finrank K
        (homogeneousSubmodule (Fin 4) K d))) =
      Module.finrank L (homogeneousSubmodule (Fin 4) L d) := by
    simp only [Fintype.card_fin]
    rw [homogeneous_polynomial_finrank, homogeneous_polynomial_finrank]
  exact hLI.span_eq_top_of_card_eq_finrank' hcard

end PfaffianDescent
