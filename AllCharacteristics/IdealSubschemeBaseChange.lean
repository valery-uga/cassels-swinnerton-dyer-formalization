import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Base change of ideal-defined closed subschemes

The closed subscheme defined by a pulled-back ideal is the actual Cartesian
base change. If the ambient families form a Cartesian square, the induced
closed-subscheme families do as well.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X Y S T : Scheme.{u}}

/-- The canonical map from an ideal's pullback subscheme to its original subscheme. -/
noncomputable def idealSubschemeBaseChangeMap (I : Y.IdealSheafData) (g : X ⟶ Y) :
    (I.comap g).subscheme ⟶ I.subscheme :=
  (I.comapIso g).hom ≫ pullback.snd g I.subschemeι

/-- The pullback ideal defines the actual inverse-image closed subscheme. -/
theorem isPullback_idealSubschemeBaseChange (I : Y.IdealSheafData) (g : X ⟶ Y) :
    IsPullback (I.comap g).subschemeι (idealSubschemeBaseChangeMap I g) g I.subschemeι := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso g) (I.comapIso_hom_fst g) rfl
  change (I.comap g).subschemeι ≫ g =
    ((I.comapIso g).hom ≫ pullback.snd g I.subschemeι) ≫ I.subschemeι
  rw [← I.comapIso_hom_fst g, Category.assoc, Category.assoc, pullback.condition]

/-- A Cartesian change of ambient family also changes the closed subscheme
by the same Cartesian base change. -/
theorem isPullback_idealSubschemeFamily (I : Y.IdealSheafData)
    (g : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ T) (b : S ⟶ T)
    (h : IsPullback g p q b) :
    IsPullback (idealSubschemeBaseChangeMap I g) ((I.comap g).subschemeι ≫ p)
      (I.subschemeι ≫ q) b :=
  (isPullback_idealSubschemeBaseChange I g).flip.paste_vert h

end AllCharacteristics
