import AllCharacteristics.FiniteCoefficientField
import AllCharacteristics.FiniteBasisFieldModel
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finite field extensions descend with their exact degree

A finite extension and finitely many of its elements descend to a finite
extension of a finitely generated subfield of the original coefficient field.
The descent retains the exact dimension, any auxiliary finite coefficient
set, and the original scalar and element embeddings. Inseparability causes
no exception: the construction uses a basis multiplication table.
-/

open Module
namespace AllCharacteristics
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]

/-- Descend a finite extension and finitely many of its elements while
retaining its full degree and any prescribed finite set of base coefficients. -/
theorem exists_fg_subfield_model_of_finite_extension (s : Finset k) (t : Finset L) :
    ∃ F : Subfield k, Field.FG F ∧ (s : Set k) ⊆ F ∧
      ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : Module.Finite F E)
        (c : E →+* L),
        Module.finrank F E = Module.finrank k L ∧
        (∀ a : F, c (algebraMap F E a) = algebraMap k L a.1) ∧
        (t : Set L) ⊆ Set.range c := by
  classical
  let b := Module.finBasis k L
  obtain ⟨v, h1, hm, ht⟩ := exists_finite_basis_coefficients b t
  obtain ⟨F, hF, hcoeff⟩ := exists_fg_subfield_containing_finset (s ∪ v)
  have hs : (s : Set k) ⊆ F := fun x hx ↦ hcoeff (Finset.mem_union_left _ hx)
  have hv : (v : Set k) ⊆ F := fun x hx ↦ hcoeff (Finset.mem_union_right _ hx)
  have h1' : ∀ i, b.repr (1 : L) i ∈ Set.range (algebraMap F k) := by
    intro i
    exact ⟨⟨_, hv (h1 i)⟩, rfl⟩
  have hm' : ∀ i j l, b.repr (b i * b j) l ∈ Set.range (algebraMap F k) := by
    intro i j l
    exact ⟨⟨_, hv (hm i j l)⟩, rfl⟩
  obtain ⟨E, hE, hdegree, hmem⟩ := exists_intermediateField_model_of_basis_coefficients b h1' hm'
  have : Module.Finite F E := hE
  refine ⟨F, hF, hs, E, inferInstance, inferInstance, inferInstance, E.val.toRingHom,
    hdegree, ?_, ?_⟩
  · intro a
    exact E.val.commutes a
  · intro x hx
    refine ⟨⟨x, (hmem x).mpr ?_⟩, rfl⟩
    intro i
    exact ⟨⟨_, hv (ht x hx i)⟩, rfl⟩

end AllCharacteristics
