import PfaffianDescent.FiniteFlatHilbertTestPoints195

/-! SOURCE ONLY197. Identity/composition laws for ACTUAL Cartesian
finite-flat Hilbert point maps, by equality of entire ideal sheaf data. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma finiteFlatHilbertBaseChange_id197
    {X B : Scheme.{u}} (F : X ⟶ B)
    (H : IsPullback (𝟙 X) F F (𝟙 B)) (n : ℕ)
    (I : FiniteFlatHilbertPoint195 F n) :
    finiteFlatHilbertBaseChange195 (𝟙 X) F F (𝟙 B) H n I = I := by
  apply Subtype.ext
  exact I.val.comap_id

lemma finiteFlatHilbertBaseChange_comp197
    {X2 X1 X0 B2 B1 B0 : Scheme.{u}}
    (d21 : X2 ⟶ X1) (d10 : X1 ⟶ X0)
    (F2 : X2 ⟶ B2) (F1 : X1 ⟶ B1) (F0 : X0 ⟶ B0)
    (b21 : B2 ⟶ B1) (b10 : B1 ⟶ B0)
    (H21 : IsPullback d21 F2 F1 b21)
    (H10 : IsPullback d10 F1 F0 b10)
    (n : ℕ) (I : FiniteFlatHilbertPoint195 F0 n) :
    finiteFlatHilbertBaseChange195 (d21 ≫ d10) F2 F0 (b21 ≫ b10)
        (H21.paste_horiz H10) n I =
      finiteFlatHilbertBaseChange195 d21 F2 F1 b21 H21 n
        (finiteFlatHilbertBaseChange195 d10 F1 F0 b10 H10 n I) := by
  apply Subtype.ext
  exact I.val.comap_comp d21 d10

/-- The map does not depend on which proof certifies the actual square. -/
lemma finiteFlatHilbertBaseChange_proof_independent197
    {X0 X B0 B : Scheme.{u}}
    (d : X0 ⟶ X) (F0 : X0 ⟶ B0) (F : X ⟶ B) (b : B0 ⟶ B)
    (H H' : IsPullback d F0 F b) (n : ℕ) (I : FiniteFlatHilbertPoint195 F n) :
    finiteFlatHilbertBaseChange195 d F0 F b H n I =
      finiteFlatHilbertBaseChange195 d F0 F b H' n I := by
  apply Subtype.ext
  rfl

end PfaffianDescent
