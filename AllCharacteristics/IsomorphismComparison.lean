import Mathlib.CategoryTheory.EqToHom

/-!
# Coherent comparisons through equal source objects

These elementary category-theoretic identities keep the later scheme-fiber
proofs small without altering any elaboration or kernel limits.
-/

open CategoryTheory
namespace AllCharacteristics
universe v u
variable {C : Type u} [Category.{v} C]
variable {X Y Z P Q T B : C}

/-- Compare two identified objects through equality of their presentations. -/
noncomputable def isomorphismComparison (e : X ≅ P) (f : Y ≅ Q) (h : X = Y) : P ≅ Q :=
  e.symm ≪≫ eqToIso h ≪≫ f

/-- The canonical comparison respects structure maps that agree under transport. -/
theorem isomorphismComparison_hom_toBase (e : X ≅ P) (f : Y ≅ Q) (h : X = Y)
    (p : P ⟶ B) (q : Q ⟶ B) (x : X ⟶ B) (y : Y ⟶ B)
    (he : e.hom ≫ p = x) (hf : f.hom ≫ q = y) (hh : eqToHom h ≫ y = x) :
    (isomorphismComparison e f h).hom ≫ q = p := by
  change (e.inv ≫ eqToHom h ≫ f.hom) ≫ q = p
  rw [Category.assoc, Category.assoc, hf, hh]
  exact e.inv_comp_eq.mpr he.symm

/-- The comparison of a presentation with itself is the identity. -/
theorem isomorphismComparison_self (e : X ≅ P) :
    isomorphismComparison e e rfl = Iso.refl P := by
  simp [isomorphismComparison]

/-- Canonical comparisons satisfy the cocycle law. -/
theorem isomorphismComparison_comp (e : X ≅ P) (f : Y ≅ Q) (g : Z ≅ T)
    (h : X = Y) (h' : Y = Z) :
    isomorphismComparison e f h ≪≫ isomorphismComparison f g h' =
      isomorphismComparison e g (h.trans h') := by
  cases h
  cases h'
  simp [isomorphismComparison]

/-- Factoring a transported equality recovers the corresponding two-step comparison. -/
theorem isomorphismComparison_factor (e : X ≅ P) (f : Y ≅ Q)
    (h : X = Z) (h' : Z = Y) :
    isomorphismComparison e f (h.trans h') =
      (eqToIso h.symm ≪≫ e).symm ≪≫ (eqToIso h' ≪≫ f) := by
  cases h
  cases h'
  simp [isomorphismComparison]

end AllCharacteristics
