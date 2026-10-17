import AllCharacteristics.IsomorphismComparison

/-!
# Naturality of canonical isomorphism comparisons

Comparisons through equal presentations commute with maps that respect those
presentations. This provides a small categorical proof for fiber restriction.
-/

open CategoryTheory
namespace AllCharacteristics
universe v u
variable {C : Type u} [Category.{v} C]
variable {X Y X' Y' P Q P' Q' : C}

/-- A commuting square through two isomorphisms also commutes through their inverses. -/
theorem iso_inv_naturality (e' : X' ≅ P') (e : X ≅ P)
    (a : X' ⟶ X) (p : P' ⟶ P) (h : e'.hom ≫ p = a ≫ e.hom) :
    e'.inv ≫ a = p ≫ e.inv := by
  apply e'.inv_comp_eq.mpr
  rw [← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Canonical comparisons commute with maps of the identified presentations. -/
theorem isomorphismComparison_naturality (e' : X' ≅ P') (f' : Y' ≅ Q')
    (e : X ≅ P) (f : Y ≅ Q) (h' : X' = Y') (h : X = Y)
    (a : X' ⟶ X) (b : Y' ⟶ Y) (p : P' ⟶ P) (q : Q' ⟶ Q)
    (he : e'.hom ≫ p = a ≫ e.hom) (hf : f'.hom ≫ q = b ≫ f.hom)
    (hh : eqToHom h' ≫ b = a ≫ eqToHom h) :
    (isomorphismComparison e' f' h').hom ≫ q =
      p ≫ (isomorphismComparison e f h).hom := by
  change (e'.inv ≫ eqToHom h' ≫ f'.hom) ≫ q = p ≫ e.inv ≫ eqToHom h ≫ f.hom
  rw [Category.assoc, Category.assoc, hf, ← Category.assoc (eqToHom h'), hh,
    Category.assoc a, ← Category.assoc e'.inv a, iso_inv_naturality e' e a p he, Category.assoc]

end AllCharacteristics
