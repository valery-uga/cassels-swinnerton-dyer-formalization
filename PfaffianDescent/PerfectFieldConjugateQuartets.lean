import PfaffianDescent.GaloisConjugates
import PfaffianDescent.GeometricSpan
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! General position of four geometric conjugates of a nonplanar point of
degree four or five over a perfect field. The full quintic set of embeddings
and the normal target extension are constructed internally. -/

noncomputable section
namespace PfaffianDescent
open Module

universe u

theorem perfectField_conjugate_quartet_independent
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (hdim : finrank K L = 4 ∨ finrank K L = 5)
    (p : Fin 4 → L) (hp : LinearIndependent K p)
    (ev : Fin 4 → L →ₐ[K] AlgebraicClosure K) (hev : Function.Injective ev) :
    LinearIndependent (AlgebraicClosure K) (fun k j => ev k (p j)) := by
  classical
  rcases hdim with h4 | h5
  · apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · exact le_of_eq
        (geometric_span_eq_top_of_coordinates_independent h4 ev hev p hp).symm
    · simp
  · let full : Fin 5 ≃ (L →ₐ[K] AlgebraicClosure K) :=
      (Fintype.equivFinOfCardEq
        ((AlgHom.card K L (AlgebraicClosure K)).trans h5)).symm
    have hfull := quintic_conjugates_general_position h5 full full.injective p
      (geometric_span_eq_top_of_coordinates_independent h5 full full.injective p hp)
    let select : Fin 4 → Fin 5 := fun k => full.symm (ev k)
    have hselect : Function.Injective select := full.symm.injective.comp hev
    simpa only [Function.comp_def, select, Equiv.apply_symm_apply] using hfull select hselect

end PfaffianDescent
