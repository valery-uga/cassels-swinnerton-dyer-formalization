import PfaffianDescent.FiniteFlatHilbertTestPoints195
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- A genuine whole finite-flat family contained in a closed ambient produces
a genuine family inside it. The factor is the native ideal-sheaf inclusion. -/
def nativeFiniteFlatPointOfIdealContainment312
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
    (I : X.IdealSheafData) (P : FiniteFlatHilbertPoint195 F n) (h : I ≤ P.val) :
    FiniteFlatHilbertPoint195 (I.subschemeι ≫ F) n := by
  let a : P.val.subscheme ⟶ I.subscheme := Scheme.IdealSheafData.inclusion h
  have ha : a ≫ (I.subschemeι ≫ F) = P.val.subschemeι ≫ F := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  letI : IsClosedImmersion a := inferInstance
  letI : IsFinite (a ≫ (I.subschemeι ≫ F)) := ha.symm ▸ P.property.1
  letI : Flat (a ≫ (I.subschemeι ≫ F)) := ha.symm ▸ P.property.2.1
  exact closedImmersionHilbertPoint195 (I.subschemeι ≫ F) a n
    (fun y => ha.symm ▸ P.property.2.2 y)

lemma nativeFiniteFlatPointOfIdealContainment_wholeIdeal312
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
    (I : X.IdealSheafData) (P : FiniteFlatHilbertPoint195 F n) (h : I ≤ P.val) :
    (nativeFiniteFlatPointOfIdealContainment312 F n I P h).val =
      (Scheme.IdealSheafData.inclusion h).ker := rfl

/-- Returning to the original ambient recovers the original entire family
ideal. The new family does not lose its embedding or any nilpotents. -/
lemma nativeFiniteFlatPointOfIdealContainment_ambientIdeal312
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
    (I : X.IdealSheafData) (P : FiniteFlatHilbertPoint195 F n) (h : I ≤ P.val) :
    (nativeFiniteFlatPointOfIdealContainment312 F n I P h).val.map I.subschemeι = P.val := by
  rw [nativeFiniteFlatPointOfIdealContainment_wholeIdeal312,
    Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.inclusion_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι]

end PfaffianDescent
end
