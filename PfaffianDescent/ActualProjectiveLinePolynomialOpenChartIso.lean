import PfaffianDescent.ActualProjectiveLinePolynomialChartDifferentialFrame
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [CommRing K]
local notation "Iline" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))
/-- The actual polynomial chart is the ORIGINAL P1 coordinate-open scheme. -/
def actualProjectiveLinePolynomialOpenIso (b : Bool) :
    Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)) ≅
      (Proj.basicOpen (grading Iline) (coordinate Iline b) : Scheme) :=
  actualProjectiveLinePolynomialChartIso K b ≪≫
    (Proj.basicOpenIsoSpec (grading Iline) (coordinate Iline b)
      (coordinate_mem Iline b) Nat.zero_lt_one).symm

/-- Exact factorization through the ORIGINAL coordinate-open immersion. -/
theorem actualProjectiveLinePolynomialChartToLine_factorThroughOpen (b : Bool) :
    actualProjectiveLinePolynomialChartToLine K b =
      (actualProjectiveLinePolynomialOpenIso K b).hom ≫
        (Proj.basicOpen (grading Iline) (coordinate Iline b)).ι := by
  simp only [actualProjectiveLinePolynomialChartToLine,
    actualProjectiveLinePolynomialOpenIso, Iso.trans_hom, Category.assoc,
    chartι, Proj.awayι]
  rfl


end PfaffianDescent
end
