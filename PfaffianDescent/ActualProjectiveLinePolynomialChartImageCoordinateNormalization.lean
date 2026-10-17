import PfaffianDescent.ActualProjectiveLinePolynomialOpenCoordinateSections

/- SOURCE ONLY. Original image-open normalization for the named coordinate,
with all original chart/open factorization and coordinate data internally supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual map through an original open has its expected WHOLE section map. -/
theorem nativeSchemeIsoChartToAmbient_appLE_top
    {X Y : Scheme.{u}} (U : X.Opens) (a : Y ≅ (U : Scheme)) :
    (a.hom ≫ U.ι).appLE U ⊤ (by simp) = U.topIso.inv ≫ a.hom.appTop := by
  have hi : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have ha : a.hom.appLE ⊤ ⊤ (by simp) = a.hom.appTop := by
    simp [Scheme.Hom.appLE]
  have h := Scheme.Hom.appLE_comp_appLE a.hom U.ι U ⊤ ⊤ (by simp) (by simp)
  simpa only [hi, ha] using h.symm

/-- Original appIso at the image open matches appLE at its actual named open.
The equality is ordinary image identification, with no desired ring-map premise. -/
theorem nativeOpenImmersion_appIso_top_namedOpen_hom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) (hU : f ''ᵁ ⊤ = U) :
    X.presheaf.map (eqToHom hU).op ≫ (f.appIso ⊤).hom =
      f.appLE U ⊤ (by rw [← hU]; exact (f.preimage_image_eq ⊤).ge) := by
  rw [Scheme.Hom.appIso_hom']
  exact Scheme.Hom.map_appLE' f
    (show ⊤ ≤ f ⁻¹ᵁ U from by rw [← hU]; exact (f.preimage_image_eq ⊤).ge) hU

/-- Original inverse appIso sends a computed chart coordinate to its actual
ambient section, transported only along the ordinary named-image equality. -/
theorem nativeOpenImmersion_appIso_top_inv_of_namedOpen_coordinate
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) (hU : f ''ᵁ ⊤ = U)
    (q : Γ(X, U)) (r : Γ(Y, ⊤))
    (hq : f.appLE U ⊤ (by rw [← hU]; exact (f.preimage_image_eq ⊤).ge) q = r) :
    (f.appIso ⊤).inv r = X.presheaf.map (eqToHom hU).op q := by
  apply (ConcreteCategory.bijective_of_isIso (f.appIso ⊤).hom).injective
  rw [Iso.inv_hom_id_apply]
  exact (ConcreteCategory.congr_hom
    (nativeOpenImmersion_appIso_top_namedOpen_hom f U hU) q).trans hq |>.symm

/-- Image comparison handles the open-immersion instance at ABSTRACT
scheme maps, rather than dependent rewriting at the original chart. -/
private theorem originalChartFactor_image_top004
    {X Y : Scheme.{u}} (U : X.Opens) (a : Y ≅ (U : Scheme))
    (f : Y ⟶ X) [IsOpenImmersion f] (hf : f = a.hom ≫ U.ι) :
    f ''ᵁ ⊤ = U := by
  cases hf
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

/-- Actual named image implies the true top preimage bound through explicit
native preimage functor equality. No dependent ▸ inference at original factories. -/
private theorem originalTopLePreimage_of_image_top004
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) (hU : f ''ᵁ ⊤ = U) : ⊤ ≤ f ⁻¹ᵁ U := by
  have h : f ⁻¹ᵁ U = ⊤ :=
    (congrArg (fun W : X.Opens => f ⁻¹ᵁ W) hU.symm).trans (f.preimage_image_eq ⊤)
  exact h.ge

/-- Factorization is eliminated with abstract native scheme/ring indices,
BEFORE inserting the original P1 chart. Only the actual map equality is used. -/
private theorem originalChartFactor_appLE_top003
    {X Y : Scheme.{u}} (U : X.Opens) (a : Y ≅ (U : Scheme))
    (f : Y ⟶ X) (hf : f = a.hom ≫ U.ι) (hU : ⊤ ≤ f ⁻¹ᵁ U) :
    f.appLE U ⊤ hU = U.topIso.inv ≫ a.hom.appTop := by
  cases hf
  exact nativeSchemeIsoChartToAmbient_appLE_top U a

attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [CommRing K]
local notation "Iline" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- SAME original polynomial chart has image exactly the original coordinate open. -/
theorem actualProjectiveLinePolynomialChartToLine_image_top (b : Bool) :
    actualProjectiveLinePolynomialChartToLine K b ''ᵁ ⊤ =
      Proj.basicOpen (grading Iline) (coordinate Iline b) := by
  exact originalChartFactor_image_top004
    (Proj.basicOpen (grading Iline) (coordinate Iline b))
    (actualProjectiveLinePolynomialOpenIso K b)
    (actualProjectiveLinePolynomialChartToLine K b)
    (actualProjectiveLinePolynomialChartToLine_factorThroughOpen K b)

/-- The original ambient coordinate section pulls back to the actual polynomial X. -/
theorem actualProjectiveLinePolynomialChartToLine_appLE_coordinate (b : Bool) :
    let U := Proj.basicOpen (grading Iline) (coordinate Iline b)
    (actualProjectiveLinePolynomialChartToLine K b).appLE U ⊤
      (originalTopLePreimage_of_image_top004
        (actualProjectiveLinePolynomialChartToLine K b) U
        (actualProjectiveLinePolynomialChartToLine_image_top K b))
      ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
        (chartCoordinate Iline b (!b))) =
      (Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv.hom
        (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0))) := by
  let U := Proj.basicOpen (grading Iline) (coordinate Iline b)
  let a := actualProjectiveLinePolynomialOpenIso K b
  let r := (Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv.hom
    (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0)))
  have hq := actualProjectiveLinePolynomialOpenIso_inverse_coordinate K b
  have hc : a.hom.appTop (a.inv.appTop r) = r := by
    have h : a.inv.appTop ≫ a.hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
    exact ConcreteCategory.congr_hom h r
  let q := (Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
    (chartCoordinate Iline b (!b))
  have hb : ⊤ ≤ (actualProjectiveLinePolynomialChartToLine K b) ⁻¹ᵁ U :=
    originalTopLePreimage_of_image_top004 (actualProjectiveLinePolynomialChartToLine K b) U
      (actualProjectiveLinePolynomialChartToLine_image_top K b)
  have hs := originalChartFactor_appLE_top003 U a
    (actualProjectiveLinePolynomialChartToLine K b)
    (actualProjectiveLinePolynomialChartToLine_factorThroughOpen K b) hb
  have hqi : U.topIso.inv q = a.inv.appTop r := by
    have h := congrArg (fun z : Γ(projectiveLineProj K, U) => U.topIso.inv z) hq.symm
    exact h.trans (Iso.hom_inv_id_apply U.topIso (a.inv.appTop r))
  have hforward : a.hom.appTop (U.topIso.inv q) = r :=
    (congrArg (fun z : Γ((U : Scheme), ⊤) => a.hom.appTop z) hqi).trans hc
  exact (ConcreteCategory.congr_hom hs q).trans hforward

/-- EXACT original appIso inverse coordinate, the input needed by the genuine
open-differential comparison. No image/coefficient certificate input at this caller. -/
theorem actualProjectiveLinePolynomialChartToLine_appIso_inverse_coordinate (b : Bool) :
    ((actualProjectiveLinePolynomialChartToLine K b).appIso ⊤).inv
      ((Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv.hom
        (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0)))) =
      (projectiveLineProj K).presheaf.map
        (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
        ((Proj.awayToSection (grading Iline) (coordinate Iline b)).hom
          (chartCoordinate Iline b (!b))) := by
  exact nativeOpenImmersion_appIso_top_inv_of_namedOpen_coordinate
    (actualProjectiveLinePolynomialChartToLine K b)
    (Proj.basicOpen (grading Iline) (coordinate Iline b))
    (actualProjectiveLinePolynomialChartToLine_image_top K b) _ _
    (actualProjectiveLinePolynomialChartToLine_appLE_coordinate K b)

end PfaffianDescent
end
