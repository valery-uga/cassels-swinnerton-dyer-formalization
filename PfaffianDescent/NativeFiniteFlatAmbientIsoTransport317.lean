import PfaffianDescent.FiniteFlatHilbertTestPoints195
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

def nativeFiniteFlatPointProjectionEq317 {X B : Scheme.{u}}
    {F G : X ⟶ B} (h : F = G) (n : ℕ) (P : FiniteFlatHilbertPoint195 F n) :
    FiniteFlatHilbertPoint195 G n := h ▸ P

lemma nativeFiniteFlatPointProjectionEq_wholeIdeal317 {X B : Scheme.{u}}
    {F G : X ⟶ B} (h : F = G) (n : ℕ) (P : FiniteFlatHilbertPoint195 F n) :
    (nativeFiniteFlatPointProjectionEq317 h n P).val = P.val := by
  cases h
  rfl

private lemma nativeAmbientIsoInverse_toBase317 {X Y B : Scheme.{u}}
    (F : X ⟶ B) (G : Y ⟶ B) (e : X ≅ Y) (h : e.hom ≫ G = F) :
    e.inv ≫ F = G :=
  (congrArg (fun f : X ⟶ B => e.inv ≫ f) h.symm).trans (e.inv_hom_id_assoc G)

private lemma nativeAmbientIsoInverse_isPullback317 {X Y B : Scheme.{u}}
    (F : X ⟶ B) (G : Y ⟶ B) (e : X ≅ Y) (h : e.hom ≫ G = F) :
    IsPullback e.inv G F (𝟙 B) :=
  IsPullback.of_horiz_isIso_mono
    ⟨(nativeAmbientIsoInverse_toBase317 F G e h).trans (Category.comp_id G).symm⟩

/-- Native whole point transport, preserving the original base and rank. -/
def nativeFiniteFlatPointAmbientIso317 {X Y B : Scheme.{u}}
    (F : X ⟶ B) (G : Y ⟶ B) (e : X ≅ Y) (h : e.hom ≫ G = F)
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F n) : FiniteFlatHilbertPoint195 G n :=
  finiteFlatHilbertBaseChange195 e.inv G F (𝟙 B)
    (nativeAmbientIsoInverse_isPullback317 F G e h) n P

lemma nativeFiniteFlatPointAmbientIso_wholeIdeal317 {X Y B : Scheme.{u}}
    (F : X ⟶ B) (G : Y ⟶ B) (e : X ≅ Y) (h : e.hom ≫ G = F)
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F n) :
    (nativeFiniteFlatPointAmbientIso317 F G e h n P).val = P.val.comap e.inv := rfl

/-- Actual native point equivalence; no classification or equality outcome
is supplied in addition to the physical ambient isomorphism over the base. -/
def nativeFiniteFlatPointAmbientIsoEquiv317 {X Y B : Scheme.{u}}
    (F : X ⟶ B) (G : Y ⟶ B) (e : X ≅ Y) (h : e.hom ≫ G = F) (n : ℕ) :
    FiniteFlatHilbertPoint195 F n ≃ FiniteFlatHilbertPoint195 G n := by
  let hi := nativeAmbientIsoInverse_toBase317 F G e h
  refine { toFun := nativeFiniteFlatPointAmbientIso317 F G e h n
           invFun := nativeFiniteFlatPointAmbientIso317 G F e.symm hi n
           left_inv := ?_, right_inv := ?_ }
  · intro P
    apply Subtype.ext
    exact (P.val.comap_comp e.hom e.inv).symm.trans
      ((congrArg P.val.comap e.hom_inv_id).trans P.val.comap_id)
  · intro P
    apply Subtype.ext
    exact (P.val.comap_comp e.inv e.hom).symm.trans
      ((congrArg P.val.comap e.inv_hom_id).trans P.val.comap_id)

end PfaffianDescent
end
