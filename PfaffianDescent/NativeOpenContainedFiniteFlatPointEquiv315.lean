import PfaffianDescent.RelativeOpenFiniteFlatFamilyTransport315
import AllCharacteristics.FiniteSubschemeFromImmersion

/-! SOURCE ONLY315: genuine inverse on the entire-family open-containment
image. The open factor and all finite-flat properties are constructed from
original P. No supplied chart point, exactness or representation premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Y X B : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
variable (F : X ⟶ B) (n : ℕ)
variable (P : FiniteFlatHilbertPoint195 F n)
variable (h : Set.range P.val.subschemeι ⊆ Set.range j)

/-- Factor the ENTIRE original subscheme through the actual ambient open. -/
def nativeOpenContainedSourceLift315 : P.val.subscheme ⟶ Y :=
  IsOpenImmersion.lift j P.val.subschemeι h

lemma nativeOpenContainedSourceLift_fac315 :
    nativeOpenContainedSourceLift315 j F n P h ≫ j = P.val.subschemeι :=
  IsOpenImmersion.lift_fac _ _ _

lemma nativeOpenContainedSourceLift_isClosed315 :
    IsClosedImmersion (nativeOpenContainedSourceLift315 j F n P h) := by
  letI : IsClosedImmersion (nativeOpenContainedSourceLift315 j F n P h ≫ j) :=
    (nativeOpenContainedSourceLift_fac315 j F n P h).symm ▸ inferInstance
  exact IsClosedImmersion.of_comp (nativeOpenContainedSourceLift315 j F n P h) j

/-- Original finite-flat point lifts into the open, with SAME source/base map. -/
def nativeOpenContainedFiniteFlatPointLift315 : FiniteFlatHilbertPoint195 (j ≫ F) n := by
  let a := nativeOpenContainedSourceLift315 j F n P h
  have hb : a ≫ (j ≫ F) = P.val.subschemeι ≫ F :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun g => g ≫ F) (nativeOpenContainedSourceLift_fac315 j F n P h))
  letI : IsClosedImmersion a := nativeOpenContainedSourceLift_isClosed315 j F n P h
  letI : IsFinite (a ≫ (j ≫ F)) := hb.symm ▸ P.property.1
  letI : Flat (a ≫ (j ≫ F)) := hb.symm ▸ P.property.2.1
  exact closedImmersionHilbertPoint195 (j ≫ F) a n (fun b => hb.symm ▸ P.property.2.2 b)

lemma nativeOpenContainedFiniteFlatPointLift_wholeIdeal315 :
    (nativeOpenContainedFiniteFlatPointLift315 j F n P h).val =
      (nativeOpenContainedSourceLift315 j F n P h).ker := rfl

lemma nativeOpenContainedFiniteFlatPointLift_comap315 :
    (nativeOpenContainedFiniteFlatPointLift315 j F n P h).val = P.val.comap j := by
  have H : IsPullback (𝟙 P.val.subscheme)
      (nativeOpenContainedSourceLift315 j F n P h) P.val.subschemeι j :=
    IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp _).trans
      (nativeOpenContainedSourceLift_fac315 j F n P h).symm⟩
  exact (wholeIdeal_comap_eq_of_isPullback195 (𝟙 P.val.subscheme)
    (nativeOpenContainedSourceLift315 j F n P h) P.val.subschemeι j H).symm.trans
      (congrArg (fun I => I.comap j) P.val.ker_subschemeι)

variable [IsSeparated F]

lemma nativeOpenContainedFiniteFlatPoint_push_lift315 :
    nativeFiniteFlatPointPushOpen314 j F n
      (nativeOpenContainedFiniteFlatPointLift315 j F n P h) = P := by
  apply Subtype.ext
  exact (nativeFiniteFlatPointPushOpen_wholeIdeal314 j F n
    (nativeOpenContainedFiniteFlatPointLift315 j F n P h)).trans
      ((Scheme.IdealSheafData.map_ker _ _).trans
        ((congrArg (fun g => g.ker) (nativeOpenContainedSourceLift_fac315 j F n P h)).trans
          P.val.ker_subschemeι))

/-- The pushed ORIGINAL chart point's entire subscheme is in the ambient open. -/
lemma nativeFiniteFlatPointPushOpen_range315 (Q : FiniteFlatHilbertPoint195 (j ≫ F) n) :
    Set.range (nativeFiniteFlatPointPushOpen314 j F n Q).val.subschemeι ⊆ Set.range j := by
  have hb : (Q.val.subschemeι ≫ j) ≫ F = Q.val.subschemeι ≫ (j ≫ F) := Category.assoc _ _ _
  letI : IsFinite ((Q.val.subschemeι ≫ j) ≫ F) := hb.symm ▸ Q.property.1
  letI : IsClosedImmersion (Q.val.subschemeι ≫ j) :=
    nativeFiniteClosedThroughOpen_isClosed314 Q.val.subschemeι j F
  let e : Q.val.subscheme ≅ (Q.val.subschemeι ≫ j).ker.subscheme := asIso (Q.val.subschemeι ≫ j).toImage
  have he : e.hom ≫ (nativeFiniteFlatPointPushOpen314 j F n Q).val.subschemeι =
      Q.val.subschemeι ≫ j := (Q.val.subschemeι ≫ j).toImage_imageι
  have hi : e.inv ≫ (Q.val.subschemeι ≫ j) =
      (nativeFiniteFlatPointPushOpen314 j F n Q).val.subschemeι := by
    exact (congrArg (fun g : Q.val.subscheme ⟶ X => e.inv ≫ g) he.symm).trans
      (e.inv_hom_id_assoc (nativeFiniteFlatPointPushOpen314 j F n Q).val.subschemeι)
  rintro _ ⟨z, rfl⟩
  refine ⟨Q.val.subschemeι (e.inv z), ?_⟩
  exact congrArg (fun g : (nativeFiniteFlatPointPushOpen314 j F n Q).val.subscheme ⟶ X => g z) hi

lemma nativeOpenContainedFiniteFlatPoint_lift_push315
    (Q : FiniteFlatHilbertPoint195 (j ≫ F) n)
    (hQ : Set.range (nativeFiniteFlatPointPushOpen314 j F n Q).val.subschemeι ⊆ Set.range j) :
    nativeOpenContainedFiniteFlatPointLift315 j F n (nativeFiniteFlatPointPushOpen314 j F n Q) hQ = Q := by
  have hb : (Q.val.subschemeι ≫ j) ≫ F = Q.val.subschemeι ≫ (j ≫ F) := Category.assoc _ _ _
  letI : IsFinite ((Q.val.subschemeι ≫ j) ≫ F) := hb.symm ▸ Q.property.1
  letI : IsClosedImmersion (Q.val.subschemeι ≫ j) :=
    nativeFiniteClosedThroughOpen_isClosed314 Q.val.subschemeι j F
  apply Subtype.ext
  exact (nativeOpenContainedFiniteFlatPointLift_comap315 j F n
    (nativeFiniteFlatPointPushOpen314 j F n Q) hQ).trans
      ((congrArg (fun I => I.comap j) (nativeFiniteFlatPointPushOpen_wholeIdeal314 j F n Q)).trans
        (nativeEmbeddedIdealComapMap315 j Q.val))

/-- Equivalence with the geometric ENTIRE-family open-containment image.
This is not an assumed chart equivalence or parameter-space representation. -/
def nativeOpenContainedFiniteFlatPointEquiv315 :
    FiniteFlatHilbertPoint195 (j ≫ F) n ≃
      {P : FiniteFlatHilbertPoint195 F n // Set.range P.val.subschemeι ⊆ Set.range j} where
  toFun Q := ⟨nativeFiniteFlatPointPushOpen314 j F n Q, nativeFiniteFlatPointPushOpen_range315 j F n Q⟩
  invFun P := nativeOpenContainedFiniteFlatPointLift315 j F n P.val P.property
  left_inv Q := nativeOpenContainedFiniteFlatPoint_lift_push315 j F n Q _
  right_inv P := Subtype.ext (nativeOpenContainedFiniteFlatPoint_push_lift315 j F n P.val P.property)

end PfaffianDescent
end
