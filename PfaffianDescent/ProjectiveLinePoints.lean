import PfaffianDescent.LineGrassmannianProjIso

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
section
variable (K : Type u) [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- A normalized pair of homogeneous coordinates defines an actual section of the Proj projective line. -/
noncomputable def projectiveLinePoint (b : Bool) (a : K) : Spec (.of K) ⟶ projectiveLineProj K :=
  grassmannianChartEvaluation K (lineChartMatrix K a) ≫
    grassmannianChartι K (lineChartPermutation b) ≫ (lineGrassmannianProjIso K).hom

lemma projectiveLinePoint_toBase (b : Bool) (a : K) :
    projectiveLinePoint K b a ≫ projectiveLineProjToBase K = 𝟙 _ := by
  change (_ ≫ (_ ≫ (lineGrassmannianProjIso K).hom)) ≫ projectiveLineProjToBase K = _
  rw [Category.assoc, Category.assoc, lineGrassmannianProjIso_toBase, grassmannianChartι_toBase]
  simpa using grassmannianChartEvaluation_toBase K (lineChartMatrix K a)

/-- Zero and infinity are the zero slopes in the two standard projective-line charts. -/
noncomputable def projectiveLineEndpoint (b : Bool) : Spec (.of K) ⟶ projectiveLineProj K :=
  projectiveLinePoint K b 0

lemma projectiveLineEndpoint_toBase (b : Bool) :
    projectiveLineEndpoint K b ≫ projectiveLineProjToBase K = 𝟙 _ :=
  projectiveLinePoint_toBase K b 0

end
end PfaffianDescent
