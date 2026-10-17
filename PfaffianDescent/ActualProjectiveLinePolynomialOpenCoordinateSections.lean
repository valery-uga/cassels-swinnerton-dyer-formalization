import PfaffianDescent.ActualProjectiveLinePolynomialOpenChartIso

/- SOURCE ONLY / UNVERIFIED. WHOLE native coefficient diagram and named
coordinate action of the ORIGINAL P1 polynomial/open chart Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [CommRing K]
local notation "Iline" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- WHOLE ORIGINAL section-ring comparison, including ORIGINAL chart ring
polynomial presentation, original GammaSpec map and original open topIso. -/
theorem actualProjectiveLinePolynomialOpenIso_inverse_topSection_square (b : Bool) :
    let U := Proj.basicOpen (grading Iline) (coordinate Iline b)
    (Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv ≫
      (actualProjectiveLinePolynomialOpenIso K b).inv.appTop ≫ U.topIso.hom =
        CommRingCat.ofHom (chartPolynomialEquiv (R := K) b).toRingHom ≫
          Proj.awayToSection (grading Iline) (coordinate Iline b) := by
  let U := Proj.basicOpen (grading Iline) (coordinate Iline b)
  let e := chartPolynomialEquiv (R := K) b
  change (Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv ≫
    (Spec.map (CommRingCat.ofHom e.toRingHom)).appTop ≫
      (Proj.basicOpenToSpec (grading Iline) (coordinate Iline b)).appTop ≫ U.topIso.hom = _
  have hbasic :
      (Proj.basicOpenToSpec (grading Iline) (coordinate Iline b)).appTop =
        (Scheme.ΓSpecIso (.of (ChartRing Iline b))).hom ≫
          Proj.awayToSection (grading Iline) (coordinate Iline b) ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top (grading Iline) (coordinate Iline b)
  rw [hbasic]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc (CommRingCat.ofHom e.toRingHom)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The coordinate transported by ORIGINAL polynomial/open Iso is EXACTLY
the actual normalized P1 coordinate section t/s (or s/t), not an independent choice. -/
theorem actualProjectiveLinePolynomialOpenIso_inverse_coordinate (b : Bool) :
    let U := Proj.basicOpen (grading Iline) (coordinate Iline b)
    U.topIso.hom
      ((actualProjectiveLinePolynomialOpenIso K b).inv.appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial {i : Bool // i ≠ b} K))).inv
          (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0))))) =
      (Proj.awayToSection (grading Iline) (coordinate Iline b))
        (chartCoordinate Iline b (!b)) := by
  have h := ConcreteCategory.congr_hom
    (actualProjectiveLinePolynomialOpenIso_inverse_topSection_square K b)
    (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0)))
  have hx : chartPolynomialEquiv (R := K) b
      (MvPolynomial.X (lineProjectiveVariableEquiv b (0, 0))) =
        chartCoordinate Iline b (!b) :=
    projectiveChartPolynomialEquiv_X K b (lineProjectiveVariableEquiv b (0, 0))
  exact h.trans (congrArg (fun q =>
    (Proj.awayToSection (grading Iline) (coordinate Iline b)) q) hx)

end PfaffianDescent
end
