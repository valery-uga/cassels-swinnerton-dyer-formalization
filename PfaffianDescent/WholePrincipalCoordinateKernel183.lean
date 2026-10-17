import PfaffianDescent.PrescribedAffineCoordinateKernel183
import PfaffianDescent.PrincipalTensorCoordinates181

/-! Source-only183: the whole ideal transported181 is literally180's old
quotient kernel. Transport179's OLD regular pair to that EXACT kernel. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire actual coordinate kernel in the constructed tensor chart
is the entire original affine ideal localized179 and transported181. -/
lemma principalTensorChart_whole_coordinate_kernel183
    {B : Type u} [CommRing B] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (f : Γ(X, U)) (e : Localization.Away f ≃+* B)
    (j : Z ⟶ Spec (.of B)) [IsClosedImmersion j]
    (hfac : j ≫ principalTensorChart181 U f e = i) :
    closedAffineCoordinateIdeal180 j =
      ((i.ker.ideal U).map (algebraMap Γ(X, U) (Localization.Away f))).map e.toRingHom := by
  let V : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
  let Esec := (principalAffineSectionsEquiv181 U f).symm.trans e
  letI := principalTensorChart181_isOpenImmersion U f e
  have hwhole := closedAffineCoordinateIdeal_eq_prescribed_coordinates183
    i V Esec (principalTensorChart181 U f e)
      (principalTensorChart181_section_coordinates U f e) j hfac
  exact hwhole.trans (principalTensorChart181_whole_ideal i U f e)

/-- An OLD179 pair now describes the exact ideal used by the SAME-Z180
quotient and required174. The target ideal/pair properties are conclusions. -/
lemma principalTensorChart_coordinate_regular_pair183
    {B : Type u} [CommRing B] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (f : Γ(X, U)) (e : Localization.Away f ≃+* B)
    (j : Z ⟶ Spec (.of B)) [IsClosedImmersion j]
    (hfac : j ≫ principalTensorChart181 U f e = i)
    (a b : Localization.Away f)
    (hgen : (i.ker.ideal U).map (algebraMap Γ(X, U) (Localization.Away f)) =
      Ideal.span ({a, b} : Set (Localization.Away f)))
    (ha : a ∈ (Localization.Away f)⁰)
    (hb : Ideal.Quotient.mk (Ideal.span ({a} : Set (Localization.Away f))) b ∈
      ((Localization.Away f) ⧸ Ideal.span ({a} : Set (Localization.Away f)))⁰) :
    closedAffineCoordinateIdeal180 j = Ideal.span ({e a, e b} : Set B) ∧
      e a ∈ B⁰ ∧ Ideal.Quotient.mk (Ideal.span ({e a} : Set B)) (e b) ∈
        (B ⧸ Ideal.span ({e a} : Set B))⁰ := by
  obtain ⟨hspan, hA, hB⟩ := tensorCoordinates181_regular_pair
    f e (i.ker.ideal U) a b hgen ha hb
  exact ⟨(principalTensorChart_whole_coordinate_kernel183 i U f e j hfac).trans hspan,
    hA, hB⟩

end PfaffianDescent
