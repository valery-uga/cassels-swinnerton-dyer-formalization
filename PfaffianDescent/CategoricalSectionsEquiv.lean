import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits
universe v u
section
variable {C : Type u} [Category.{v} C] {P X Y B Z : C}
    {p : P ⟶ X} {q : P ⟶ Y} {i : X ⟶ B} {j : Y ⟶ B}

/-- The pullback universal property as an equivalence of sections over a fixed base map. -/
noncomputable def pullbackSectionsEquiv (H : IsPullback p q i j) (g : Z ⟶ X) :
    {f : Z ⟶ Y // f ≫ j = g ≫ i} ≃ {a : Z ⟶ P // a ≫ p = g} where
  toFun f := ⟨H.lift g f.1 f.2.symm, H.lift_fst _ _ _⟩
  invFun a := ⟨a.1 ≫ q, by rw [Category.assoc, ← H.w, ← Category.assoc, a.2]⟩
  left_inv f := Subtype.ext (H.lift_snd _ _ _)
  right_inv a := by
    apply Subtype.ext
    apply H.hom_ext
    · exact (H.lift_fst _ _ _).trans a.2.symm
    · exact H.lift_snd _ _ _

end
section
variable {C : Type u} [Category.{v} C] {P Q B Z : C}

/-- An isomorphism over the base identifies sections on every test object. -/
noncomputable def isoSectionsEquiv (e : P ≅ Q) (p : P ⟶ B) (q : Q ⟶ B)
    (he : e.hom ≫ q = p) (g : Z ⟶ B) :
    {a : Z ⟶ P // a ≫ p = g} ≃ {b : Z ⟶ Q // b ≫ q = g} where
  toFun a := ⟨a.1 ≫ e.hom, by rw [Category.assoc, he, a.2]⟩
  invFun b := ⟨b.1 ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc, b.2]⟩
  left_inv a := by apply Subtype.ext; simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv b := by apply Subtype.ext; simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

end
end PfaffianDescent
