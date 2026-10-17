import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.CommAlgCat.Basic

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Equality of original coefficient-ring squares gives the genuine
contravariant Scheme square, without reducing concrete chart objects. -/
lemma nativeRingSquareSpec300
    {X Y Z W : Type u} [CommRing X] [CommRing Y] [CommRing Z] [CommRing W]
    (f : Y →+* X) (g : Z →+* Y) (a : W →+* X) (b : Z →+* W)
    (h : f.comp g = a.comp b) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, h]

/-- A derived threefold coefficient identity gives the actual Spec cocycle. -/
lemma nativeAlgebraTripleSpec_cycle300
    {R X Y Z : Type u} [CommRing R] [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra R X] [Algebra R Y] [Algebra R Z]
    (f : Y →ₐ[R] X) (g : Z →ₐ[R] Y) (h : X →ₐ[R] Z)
    (hc : f.comp (g.comp h) = AlgHom.id R X) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom h.toRingHom) = 𝟙 (Spec (.of X)) := by
  have hr : f.toRingHom.comp (g.toRingHom.comp h.toRingHom) = RingHom.id X :=
    congrArg (fun z => z.toRingHom) hc
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hr, CommRingCat.ofHom_id, Spec.map_id]

/-- Native actual pullbacks are transported to the ORIGINAL open-subscheme
presentation through original side Isos and exact inclusion squares. -/
lemma nativePullbackSidesTransport300
    {C : Type*} [Category C] {P X Y Z X' Y' : C}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (eX : X ≅ X') (eY : Y ≅ Y')
    (i : X' ⟶ Z) (j : Y' ⟶ Z)
    (hi : eX.hom ≫ i = f) (hj : eY.hom ≫ j = g) :
    IsPullback (fst ≫ eX.hom) (snd ≫ eY.hom) i j := by
  apply h.of_iso (Iso.refl P) eX eY (Iso.refl Z)
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.comp_id] using hi.symm
  · simpa only [Iso.refl_hom, Category.comp_id] using hj.symm

lemma nativePrincipalPairTransition_fac300
    {C : Type*} [Category C] {X Y X' Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (a : X ≅ Y) :
    eX.hom ≫ (eX.symm ≪≫ a ≪≫ eY).hom = a.hom ≫ eY.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The actual triple rotation cocycle remains a cocycle after the exact
identification of each triple domain with its native original pullback. -/
lemma nativeTripleConjugate_cycle300
    {C : Type*} [Category C] {P Q S P' Q' S' : C}
    (eP : P ≅ P') (eQ : Q ≅ Q') (eS : S ≅ S')
    (r : P ⟶ Q) (s : Q ⟶ S) (t : S ⟶ P) (h : r ≫ s ≫ t = 𝟙 P) :
    (eP.inv ≫ r ≫ eQ.hom) ≫ (eQ.inv ≫ s ≫ eS.hom) ≫
        (eS.inv ≫ t ≫ eP.hom) = 𝟙 P' := by
  calc
    _ = eP.inv ≫ (r ≫ s ≫ t) ≫ eP.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = eP.inv ≫ 𝟙 P ≫ eP.hom := congrArg (fun z => eP.inv ≫ z ≫ eP.hom) h
    _ = _ := by simp only [Category.id_comp, Iso.inv_hom_id]

/-- An internally derived projection square gives exactly GlueData.t_fac
 after conjugating genuine original triple domains. -/
lemma nativeTripleConjugate_fac300
    {C : Type*} [Category C] {P Q P' Q' X Y : C}
    (eP : P ≅ P') (eQ : Q ≅ Q') (r : P ⟶ Q)
    (a : Q' ⟶ Y) (b : P' ⟶ X) (t : X ⟶ Y)
    (h : r ≫ eQ.hom ≫ a = eP.hom ≫ b ≫ t) :
    (eP.inv ≫ r ≫ eQ.hom) ≫ a = b ≫ t := by
  calc
    _ = eP.inv ≫ (r ≫ eQ.hom ≫ a) := by simp only [Category.assoc]
    _ = eP.inv ≫ (eP.hom ≫ b ≫ t) := congrArg (fun z => eP.inv ≫ z) h
    _ = _ := by simp only [Iso.inv_hom_id_assoc]

end PfaffianDescent
