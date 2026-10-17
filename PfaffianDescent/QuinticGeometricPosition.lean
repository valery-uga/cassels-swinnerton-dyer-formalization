import PfaffianDescent.GaloisConjugates
import PfaffianDescent.GeometricSpan
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Galois.Basic

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable (K A : Type*) [Field K] [Field A] [Algebra K A]

/-- A concrete splitting field, formed inside the algebraic closure from the
images of all ground-field embeddings of the residue extension. -/
noncomputable abbrev QuinticSplittingField := IntermediateField.normalClosure K A (AlgebraicClosure K)

end

section
variable {K A : Type*} [Field K] [CharZero K] [Field A] [Algebra K A]
    [FiniteDimensional K A]

instance : IsGalois K (QuinticSplittingField K A) := ⟨⟩

/-- A degree-five extension has exactly five distinct embeddings into the
constructed finite Galois splitting field. -/
noncomputable def quinticSplittingEmbeddings (hdim : finrank K A = 5) :
    Fin 5 ≃ (A →ₐ[K] QuinticSplittingField K A) :=
  (Fintype.equivFinOfCardEq ((AlgHom.card K A (AlgebraicClosure K)).trans hdim)).symm.trans
    (normalClosure.algHomEquiv K A (AlgebraicClosure K)).symm

/-- The constructed splitting field is a finite Galois extension. -/
theorem quinticSplittingField_finite_galois :
    FiniteDimensional K (QuinticSplittingField K A) ∧ IsGalois K (QuinticSplittingField K A) :=
  ⟨inferInstance, inferInstance⟩

/-- Four independent coordinate functions of a degree-five point produce five
geometric conjugates in general linear position. -/
theorem quintic_independent_coordinates_general_position (hdim : finrank K A = 5)
    (p : Vec A 4) (hp : LinearIndependent K p) :
    FivePointGeneralPosition (fun i j => quinticSplittingEmbeddings hdim i (p j)) := by
  let ev := quinticSplittingEmbeddings hdim
  apply quintic_conjugates_general_position hdim ev ev.injective p
  exact geometric_span_eq_top_of_coordinates_independent hdim ev ev.injective p hp

/-- The coplanar and general-position cases exhaust degree-five points. The
plane equation and finite Galois splitting field are both constructed here. -/
theorem quintic_coordinate_position_dichotomy (hdim : finrank K A = 5) (p : Vec A 4) :
    (∃ c : Fin 4 → K, c ≠ 0 ∧ ∑ j, c j • p j = 0) ∨
    FivePointGeneralPosition (fun i j => quinticSplittingEmbeddings hdim i (p j)) := by
  by_cases hp : LinearIndependent K p
  · exact Or.inr (quintic_independent_coordinates_general_position hdim p hp)
  · left
    obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hp
    refine ⟨c, ?_, hc⟩
    intro h
    exact hj (congrFun h j)

end
end PfaffianDescent
