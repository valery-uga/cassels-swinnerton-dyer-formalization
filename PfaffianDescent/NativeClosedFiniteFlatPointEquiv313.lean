import PfaffianDescent.NativeWholeIdealContainment312
import PfaffianDescent.NativeFiniteFlatClosedAmbientFactor312
import PfaffianDescent.NativeClosedChartBaseChange312

/-! SOURCE ONLY313. Genuine closed-ambient whole finite-flat families. The
factor returns to the ORIGINAL closed immersion's source by its native
source-to-image Iso. Neither a support model nor an inverse-family certificate
is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- A closed embedding reflects its entire source ideal after map and comap. -/
lemma nativeWholeIdeal_comap_map_closed313 {Z X : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] (J : Z.IdealSheafData) :
    (J.map j).comap j = J := by
  have H : IsPullback (𝟙 J.subscheme) J.subschemeι (J.subschemeι ≫ j) j :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  exact (wholeIdeal_comap_eq_of_isPullback195 (𝟙 J.subscheme) J.subschemeι
    (J.subschemeι ≫ j) j H).trans J.ker_subschemeι

lemma nativeWholeIdeal_map_closed_injective313 {Z X : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] : Function.Injective (fun J : Z.IdealSheafData => J.map j) := by
  intro J K he
  exact (nativeWholeIdeal_comap_map_closed313 j J).symm.trans
    ((congrArg (fun L : X.IdealSheafData => L.comap j) he).trans
      (nativeWholeIdeal_comap_map_closed313 j K))

lemma nativeWholeIdeal_map_comap_iso313 {Z Y : Scheme.{u}}
    (e : Z ≅ Y) (J : Y.IdealSheafData) : (J.comap e.hom).map e.hom = J := by
  apply le_antisymm
  · have hh := Scheme.IdealSheafData.comap_mono e.inv
      (Scheme.IdealSheafData.comap_map_le (J.comap e.hom) e.hom)
    simpa only [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id] using hh
  · exact J.le_map_comap e.hom

private lemma nativeWholeIdeal_comap_iso_then_map313 {Z Y X : Scheme.{u}}
    (e : Z ≅ Y) (j : Y ⟶ X) (J : Y.IdealSheafData) :
    (J.comap e.hom).map (e.hom ≫ j) = J.map j :=
  ((J.comap e.hom).map_comp e.hom j).trans
    (congrArg (fun K : Y.IdealSheafData => K.map j) (nativeWholeIdeal_map_comap_iso313 e J))

variable {Z X B : Scheme.{u}} (F0 : Z ⟶ B) (F : X ⟶ B)
variable (j : Z ⟶ X) [IsClosedImmersion j] (hF : j ≫ F = F0) (n : ℕ)

/-- Native original finite-flat family embedded in the same ambient. -/
def nativeClosedFiniteFlatPointPush313 (Q : FiniteFlatHilbertPoint195 F0 n) :
    FiniteFlatHilbertPoint195 F n := by
  have hb : (Q.val.subschemeι ≫ j) ≫ F = Q.val.subschemeι ≫ F0 :=
    (Category.assoc _ _ _).trans (congrArg (fun k => Q.val.subschemeι ≫ k) hF)
  letI : IsFinite ((Q.val.subschemeι ≫ j) ≫ F) := hb.symm ▸ Q.property.1
  letI : Flat ((Q.val.subschemeι ≫ j) ≫ F) := hb.symm ▸ Q.property.2.1
  exact closedImmersionHilbertPoint195 F (Q.val.subschemeι ≫ j) n
    (fun y => hb.symm ▸ Q.property.2.2 y)

lemma nativeClosedFiniteFlatPointPush_wholeIdeal313 (Q : FiniteFlatHilbertPoint195 F0 n) :
    (nativeClosedFiniteFlatPointPush313 F0 F j hF n Q).val = Q.val.map j := rfl

lemma nativeClosedFiniteFlatPointPush_contained313 (Q : FiniteFlatHilbertPoint195 F0 n) :
    j.ker ≤ (nativeClosedFiniteFlatPointPush313 F0 F j hF n Q).val :=
  Q.val.subschemeι.le_ker_comp j

include hF in
/-- The actual source-to-image Iso is compatible with the ORIGINAL family map. -/
private lemma nativeClosedImageIso_family313 :
    (asIso j.toImage).hom ≫ (j.ker.subschemeι ≫ F) = F0 :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k : Z ⟶ X => k ≫ F) j.toImage_imageι).trans hF)

include hF in
/-- Factor312 is pulled back along the actual original source-to-image Iso,
so this is a point on ORIGINAL Z and ORIGINAL F0. -/
def nativeClosedFiniteFlatPointFactor313
    (P : FiniteFlatHilbertPoint195 F n) (h : j.ker ≤ P.val) :
    FiniteFlatHilbertPoint195 F0 n :=
  finiteFlatHilbertBaseChange195 (asIso j.toImage).hom F0 (j.ker.subschemeι ≫ F)
    (𝟙 B) (IsPullback.of_horiz_isIso
      ⟨(nativeClosedImageIso_family313 F0 F j hF).trans (Category.comp_id F0).symm⟩) n
    (nativeFiniteFlatPointOfIdealContainment312 F n j.ker P h)

include hF in
lemma nativeClosedFiniteFlatPointFactor_wholeIdeal313
    (P : FiniteFlatHilbertPoint195 F n) (h : j.ker ≤ P.val) :
    (nativeClosedFiniteFlatPointFactor313 F0 F j hF n P h).val =
      (nativeFiniteFlatPointOfIdealContainment312 F n j.ker P h).val.comap
        (asIso j.toImage).hom := rfl

include hF in
lemma nativeClosedFiniteFlatPointFactor_ambientIdeal313
    (P : FiniteFlatHilbertPoint195 F n) (h : j.ker ≤ P.val) :
    (nativeClosedFiniteFlatPointFactor313 F0 F j hF n P h).val.map j = P.val := by
  let e : Z ≅ j.ker.subscheme := asIso j.toImage
  let Q := nativeFiniteFlatPointOfIdealContainment312 F n j.ker P h
  change (Q.val.comap e.hom).map j = P.val
  have hj : j = e.hom ≫ j.ker.subschemeι := j.toImage_imageι.symm
  exact (congrArg (fun a : Z ⟶ X => (Q.val.comap e.hom).map a) hj).trans
    ((nativeWholeIdeal_comap_iso_then_map313 e j.ker.subschemeι Q.val).trans
      (nativeFiniteFlatPointOfIdealContainment_ambientIdeal312 F n j.ker P h))

include hF in
lemma nativeClosedFiniteFlatPoint_push_factor313
    (P : FiniteFlatHilbertPoint195 F n) (h : j.ker ≤ P.val) :
    nativeClosedFiniteFlatPointPush313 F0 F j hF n
      (nativeClosedFiniteFlatPointFactor313 F0 F j hF n P h) = P := by
  apply Subtype.ext
  exact nativeClosedFiniteFlatPointFactor_ambientIdeal313 F0 F j hF n P h

include hF in
lemma nativeClosedFiniteFlatPoint_factor_push313 (Q : FiniteFlatHilbertPoint195 F0 n) :
    nativeClosedFiniteFlatPointFactor313 F0 F j hF n
      (nativeClosedFiniteFlatPointPush313 F0 F j hF n Q)
      (nativeClosedFiniteFlatPointPush_contained313 F0 F j hF n Q) = Q := by
  apply Subtype.ext
  apply nativeWholeIdeal_map_closed_injective313 j
  exact nativeClosedFiniteFlatPointFactor_ambientIdeal313 F0 F j hF n
    (nativeClosedFiniteFlatPointPush313 F0 F j hF n Q)
    (nativeClosedFiniteFlatPointPush_contained313 F0 F j hF n Q)

include hF in
/-- Entire embedded finite-flat families in a closed source are equivalent to
ambient families containing its WHOLE defining ideal, with both inverse laws proved. -/
def nativeClosedFiniteFlatPointEquiv313 :
    FiniteFlatHilbertPoint195 F0 n ≃
      {P : FiniteFlatHilbertPoint195 F n // j.ker ≤ P.val} where
  toFun Q := ⟨nativeClosedFiniteFlatPointPush313 F0 F j hF n Q,
    nativeClosedFiniteFlatPointPush_contained313 F0 F j hF n Q⟩
  invFun P := nativeClosedFiniteFlatPointFactor313 F0 F j hF n P.val P.property
  left_inv Q := nativeClosedFiniteFlatPoint_factor_push313 F0 F j hF n Q
  right_inv P := Subtype.ext (nativeClosedFiniteFlatPoint_push_factor313 F0 F j hF n P.val P.property)

end PfaffianDescent
end
