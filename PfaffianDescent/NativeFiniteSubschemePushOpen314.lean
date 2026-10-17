import PfaffianDescent.FiniteFlatHilbertTestPoints195
import AllCharacteristics.FiniteSubschemeFromImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! SOURCE ONLY314. Genuine finite embedded families on an actual ambient
open remain CLOSED in the separated original ambient. The closedness is
proved by properness and immersion, not supplied as an endpoint premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma nativeFiniteClosedThroughOpen_isClosed314 {W Y X B : Scheme.{u}}
    (i : W ⟶ Y) [IsClosedImmersion i] (u : Y ⟶ X) [IsOpenImmersion u]
    (F : X ⟶ B) [IsSeparated F] [IsFinite ((i ≫ u) ≫ F)] :
    IsClosedImmersion (i ≫ u) := by
  letI : IsProper ((i ≫ u) ≫ F) := inferInstance
  letI : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) F
  exact IsClosedImmersion.of_isPreimmersion (i ≫ u) (i ≫ u).isClosedMap.isClosed_range

variable {Y X B : Scheme.{u}} (u : Y ⟶ X) [IsOpenImmersion u]
variable (F : X ⟶ B) [IsSeparated F] (n : ℕ)

/-- Actual finite-flat195 family pushes into ORIGINAL separated ambient,
with closedness derived internally rather than assumed for the open map. -/
def nativeFiniteFlatPointPushOpen314 (Q : FiniteFlatHilbertPoint195 (u ≫ F) n) :
    FiniteFlatHilbertPoint195 F n := by
  have hb : (Q.val.subschemeι ≫ u) ≫ F = Q.val.subschemeι ≫ (u ≫ F) :=
    Category.assoc _ _ _
  letI : IsFinite ((Q.val.subschemeι ≫ u) ≫ F) := hb.symm ▸ Q.property.1
  letI : Flat ((Q.val.subschemeι ≫ u) ≫ F) := hb.symm ▸ Q.property.2.1
  letI : IsClosedImmersion (Q.val.subschemeι ≫ u) :=
    nativeFiniteClosedThroughOpen_isClosed314 Q.val.subschemeι u F
  exact closedImmersionHilbertPoint195 F (Q.val.subschemeι ≫ u) n
    (fun b => hb.symm ▸ Q.property.2.2 b)

lemma nativeFiniteFlatPointPushOpen_wholeIdeal314 (Q : FiniteFlatHilbertPoint195 (u ≫ F) n) :
    (nativeFiniteFlatPointPushOpen314 u F n Q).val = Q.val.map u := rfl

/-- SAME genuine datum with its LFP condition also pushes from an actual open
into ORIGINAL ambient. Arbitrary base, no field/Noetherian/rank certificate. -/
def nativeFiniteSubschemeDatumPushOpen314
    (Q : AllCharacteristics.FiniteSubschemeDatum (u ≫ F) n) :
    AllCharacteristics.FiniteSubschemeDatum F n := by
  have hb : (Q.val.subschemeι ≫ u) ≫ F = Q.val.subschemeι ≫ (u ≫ F) :=
    Category.assoc _ _ _
  letI : IsFinite ((Q.val.subschemeι ≫ u) ≫ F) := hb.symm ▸ Q.property.1
  letI : Flat ((Q.val.subschemeι ≫ u) ≫ F) := hb.symm ▸ Q.property.2.1
  letI : LocallyOfFinitePresentation ((Q.val.subschemeι ≫ u) ≫ F) :=
    hb.symm ▸ Q.property.2.2.1
  letI : IsClosedImmersion (Q.val.subschemeι ≫ u) :=
    nativeFiniteClosedThroughOpen_isClosed314 Q.val.subschemeι u F
  exact AllCharacteristics.finiteSubschemeDatumOfClosedImmersion (Q.val.subschemeι ≫ u) F n
    (fun b => hb.symm ▸ Q.property.2.2.2 b)

lemma nativeFiniteSubschemeDatumPushOpen_wholeIdeal314
    (Q : AllCharacteristics.FiniteSubschemeDatum (u ≫ F) n) :
    (nativeFiniteSubschemeDatumPushOpen314 u F n Q).val = Q.val.map u := rfl

end PfaffianDescent
end
