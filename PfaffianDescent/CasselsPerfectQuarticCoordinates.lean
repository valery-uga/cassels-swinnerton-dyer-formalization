import PfaffianDescent.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-! SOURCE ONLY. The literal Cassels quartic coordinate construction over
any perfect ground field, preserving the original extension and tuple.
Only the primitive-element separability hypothesis differs from the existing
CharZero coordinate lemma; no cubic descent theorem is imported or used. -/
noncomputable section
namespace PfaffianDescent
open Module
open scoped BigOperators
universe u
variable {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- Power-basis coordinates and the degree-four minimal polynomial of their generator. -/
theorem perfectField_exists_power_basis_four (hdim : finrank K L = 4) :
    ∃ a : L, ∃ b : Basis (Fin 4) K L,
      (∀ i, b i = a^(i : ℕ)) ∧ (minpoly K a).natDegree = 4 := by
  let p := Field.powerBasisOfFiniteOfSeparable K L
  have he : p.dim = 4 := p.finrank.symm.trans hdim
  refine ⟨p.gen, p.basis.reindex (finCongr he), ?_, p.natDegree_minpoly.trans he⟩
  intro i
  rw [Basis.reindex_apply, p.basis_eq_pow]
  rfl

/-- Independent quartic coordinates are an invertible ground-field transform
of the four powers of a primitive element. -/
theorem perfectField_independentQuarticCoordinates (hdim : finrank K L = 4)
    (p : Vec L 4) (hp : LinearIndependent K p) :
    ∃ a : L, (minpoly K a).natDegree = 4 ∧
      ∃ M : Mat K 4, Function.Injective M.mulVec ∧
        p = (M.map (algebraMap K L)).mulVec (fun i => a^(i : ℕ)) := by
  obtain ⟨a, b, hb, hmin⟩ := perfectField_exists_power_basis_four hdim
  let M : Mat K 4 := fun i j => b.repr (p i) j
  let phi : Vec K 4 →ₗ[K] L := Fintype.linearCombination K b
  have hM : ∀ i, ∑ j : Fin 4, M i j • b j = p i := fun i => b.sum_repr (p i)
  have hcomp : phi ∘ M = p := by
    funext i
    exact hM i
  have hrows : LinearIndependent K M := LinearIndependent.of_comp phi (by rw [hcomp]; exact hp)
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff.mpr (Matrix.Nonsingular.of_linearIndependent_row hrows).linearIndependent_col
  refine ⟨a, hmin, M, hinj, ?_⟩
  funext i
  rw [← hM i]
  simp only [hb, Algebra.smul_def, Matrix.mulVec, dotProduct, Matrix.map_apply]


end PfaffianDescent
