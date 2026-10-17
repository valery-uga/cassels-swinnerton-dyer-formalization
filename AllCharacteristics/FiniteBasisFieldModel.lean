import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Algebra.Algebra.Operations

/-!
# Descending finite field extensions by their multiplication coefficients

Let a finite extension have a fixed basis. If a smaller coefficient field
contains the coordinates of one and all products of basis elements, the span
of that basis over the smaller field is a finite-dimensional subalgebra. It
is an intermediate field, with exactly the original extension degree. Its
elements are characterized by the basis coordinates belonging to that field.
-/

open Module
namespace AllCharacteristics
universe u v w z
variable {F : Type u} {k : Type v} {L : Type w} {ι : Type z}
  [Field F] [Field k] [Field L] [Algebra F k] [Algebra k L] [Algebra F L]
  [IsScalarTower F k L]

/-- Closure under basis products implies closure under multiplication of
the smaller-field span. -/
theorem basis_span_mul_mem_of_product_coefficients
    (b : Basis ι k L)
    (hm : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap F k))
    (x y : L) (hx : x ∈ Submodule.span F (Set.range b))
    (hy : y ∈ Submodule.span F (Set.range b)) :
    x * y ∈ Submodule.span F (Set.range b) := by
  have hmul : Submodule.span F (Set.range b) * Submodule.span F (Set.range b) ≤
      Submodule.span F (Set.range b) := by
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨i, rfl⟩, c, ⟨j, rfl⟩, rfl⟩
    exact (b.mem_span_iff_repr_mem F (b i * b j)).mpr (hm i j)
  exact hmul (Submodule.mul_mem_mul hx hy)

/-- A finite basis whose unit and multiplication coefficients descend
spans an actual intermediate field over the smaller field, with exactly the
same degree as the original extension. -/
theorem exists_intermediateField_model_of_basis_coefficients [Finite ι]
    (b : Basis ι k L)
    (h1 : ∀ i, b.repr (1 : L) i ∈ Set.range (algebraMap F k))
    (hm : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap F k)) :
    ∃ E : IntermediateField F L, Module.Finite F E ∧
      Module.finrank F E = Module.finrank k L ∧
      ∀ x : L, x ∈ E ↔ ∀ i, b.repr x i ∈ Set.range (algebraMap F k) := by
  classical
  let V := Submodule.span F (Set.range b)
  have hone : (1 : L) ∈ V := (b.mem_span_iff_repr_mem F 1).mpr h1
  let A : Subalgebra F L := V.toSubalgebra hone (basis_span_mul_mem_of_product_coefficients b hm)
  let bA : Basis ι F A := b.restrictScalars F
  have : Module.Finite F A := Module.Finite.of_basis bA
  let E := Algebra.IsAlgebraic.toIntermediateField A
  have hfinite : Module.Finite F E := inferInstanceAs (Module.Finite F A)
  refine ⟨E, hfinite, ?_, ?_⟩
  · let := Fintype.ofFinite ι
    exact (Module.finrank_eq_card_basis bA).trans (Module.finrank_eq_card_basis b).symm
  · intro x
    exact b.mem_span_iff_repr_mem F x

/-- Finitely many coefficients record the unit, multiplication table, and
any prescribed finite set of elements of a finite-dimensional field. -/
theorem exists_finite_basis_coefficients [Fintype ι]
    (b : Basis ι k L) (t : Finset L) :
    ∃ s : Finset k,
      (∀ i, b.repr (1 : L) i ∈ s) ∧
      (∀ i j l, b.repr (b i * b j) l ∈ s) ∧
      (∀ x ∈ t, ∀ i, b.repr x i ∈ s) := by
  classical
  let a := Finset.univ.image (fun i ↦ b.repr (1 : L) i)
  let c := Finset.univ.image (fun ijl : ι × ι × ι ↦ b.repr (b ijl.1 * b ijl.2.1) ijl.2.2)
  let e := t.biUnion (fun x ↦ Finset.univ.image (fun i ↦ b.repr x i))
  refine ⟨a ∪ c ∪ e, ?_, ?_, ?_⟩
  · intro i
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  · intro i j l
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(i, j, l), Finset.mem_univ _, rfl⟩))
  · intro x hx i
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨x, hx,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

end AllCharacteristics
