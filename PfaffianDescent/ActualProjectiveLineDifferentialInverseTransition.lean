import PfaffianDescent.ActualRelativeDifferentialSectionLeibniz
import PfaffianDescent.LineGrassmannianProjCharts
import AllCharacteristics.ProjectiveChartOverlap

/- SOURCE ONLY / UNVERIFIED. Actual sheafified relative differential transition
on the original projective-line Proj model; no supplied canonical-bundle Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [CommRing K] {X : Scheme.{u}}

lemma actualRelativeDifferentialSection_one
    (g : X ⟶ Spec (.of K)) (U : X.Opens) :
    actualRelativeDifferentialSection g U 1 = 0 := by
  let eta := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (schemeRelativeDifferentialsPresheaf g)).app (op U)
  change eta ((schemeRelativeDifferentialsPresheafDerivation g).d 1) = 0
  rw [(schemeRelativeDifferentialsPresheafDerivation g).d_one (op U)]
  exact eta.hom.map_zero

/-- The inverse-coordinate rule in the genuinely sheafified relative Omega. -/
lemma actualRelativeDifferentialSection_inverseCoordinates
    (g : X ⟶ Spec (.of K)) (U : X.Opens) (a b : Γ(X, U)) (hab : a * b = 1) :
    letI : Module Γ(X, U) ((schemeRelativeDifferentials g).val.obj (op U)) :=
      ((schemeRelativeDifferentials g).val.obj (op U)).isModule
    actualRelativeDifferentialSection g U b =
      -(b ^ 2) • actualRelativeDifferentialSection g U a := by
  letI : Module Γ(X, U) ((schemeRelativeDifferentials g).val.obj (op U)) :=
    ((schemeRelativeDifferentials g).val.obj (op U)).isModule
  have hba : b * a = 1 := (mul_comm b a).trans hab
  have hd := actualRelativeDifferentialSection_leibniz g U a b
  rw [hab, actualRelativeDifferentialSection_one g U] at hd
  have hs := congrArg (fun z => b • z) hd.symm
  have hs' : actualRelativeDifferentialSection g U b +
      b ^ 2 • actualRelativeDifferentialSection g U a = 0 := by
    simpa only [smul_add, smul_smul, hba, one_smul, smul_zero, pow_two] using hs
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hs'

-- ACTUAL PROJECTIVE-LINE CALLER: all reciprocal data are constructed internally.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME actual intersection D_+(s*t) of the two original P1 charts. -/
def actualProjectiveLineCoordinateOverlap (K : Type u) [CommRing K] :
    (projectiveLineProj K).Opens :=
  Proj.basicOpen (grading (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))) (coordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false * coordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) true)

/-- t/s on the actual common open, represented by the original normalized chart coordinate. -/
def actualProjectiveLineOverlapT (K : Type u) [CommRing K] :
    Γ(projectiveLineProj K, actualProjectiveLineCoordinateOverlap K) :=
  (Proj.awayToSection (grading (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)))
    (coordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false * coordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) true)).hom
      (chartOverlapLeftMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false true (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false true))

/-- s/t on the SAME common open, from the other original normalized coordinate. -/
def actualProjectiveLineOverlapTInverse (K : Type u) [CommRing K] :
    Γ(projectiveLineProj K, actualProjectiveLineCoordinateOverlap K) :=
  (Proj.awayToSection (grading (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)))
    (coordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false * coordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) true)).hom
      (chartOverlapRightMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false true (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) true false))

lemma actualProjectiveLineOverlapCoordinates_reciprocal (K : Type u) [CommRing K] :
    actualProjectiveLineOverlapT K * actualProjectiveLineOverlapTInverse K = 1 := by
  let f := (Proj.awayToSection (grading (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)))
    (coordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false * coordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) true)).hom
  change f (chartOverlapLeftMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false true (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false true)) *
    f (chartOverlapRightMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false true (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) true false)) = 1
  rw [← chartOverlapUnit_inv (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false true, ← chartOverlapUnit_val (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) false true,
    ← map_mul, Units.inv_mul, map_one]

/-- Genuine differential sections on the SAME actual projective line, over its original base.
This is a transition identity, not yet a global Omega ≅ O(-2) assertion. -/
lemma actualProjectiveLineRelativeDifferential_inverseTransition
    (K : Type u) [CommRing K] :
    let U := actualProjectiveLineCoordinateOverlap K
    letI : Module Γ(projectiveLineProj K, U)
        ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.obj (op U)) :=
      ((schemeRelativeDifferentials (projectiveLineProjToBase K)).val.obj (op U)).isModule
    actualRelativeDifferentialSection (projectiveLineProjToBase K) U
        (actualProjectiveLineOverlapTInverse K) =
      -(actualProjectiveLineOverlapTInverse K ^ 2) •
        actualRelativeDifferentialSection (projectiveLineProjToBase K) U
          (actualProjectiveLineOverlapT K) :=
  actualRelativeDifferentialSection_inverseCoordinates (projectiveLineProjToBase K)
    (actualProjectiveLineCoordinateOverlap K) (actualProjectiveLineOverlapT K)
    (actualProjectiveLineOverlapTInverse K)
    (actualProjectiveLineOverlapCoordinates_reciprocal K)

end PfaffianDescent
end
