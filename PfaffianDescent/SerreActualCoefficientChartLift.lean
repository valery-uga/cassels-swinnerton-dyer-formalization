import AllCharacteristics.ProjectiveBaseChange
import PfaffianDescent.SchemeAffineFunctions

/-! Lift an actual parameter-chart map through coefficient change. Both its
normalized coordinates and its base-coefficient functions are derived from
the actual Cartesian chart square. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] {σ : Type}
variable (φ : R →+* S)
variable (I : HomogeneousIdeal (homogeneousSubmodule σ R))
variable (J : HomogeneousIdeal (homogeneousSubmodule σ S))
variable (hIJ : I.toIdeal.map (MvPolynomial.map φ) = J.toIdeal)
variable (j : σ) {T : Scheme.{u}}
variable (a : T ⟶ Spec (.of (ChartRing I j))) (k : T ⟶ scheme J)
variable (h : a ≫ chartι I j = k ≫ projectiveCoefficientMap φ I J hIJ)

def serreActualCoefficientChartLift : T ⟶ Spec (.of (ChartRing J j)) :=
  (isPullback_projectiveCoefficientMap_chart φ I J hIJ j).lift a k h

@[reassoc]
theorem serreActualCoefficientChartLift_toChart :
    serreActualCoefficientChartLift φ I J hIJ j a k h ≫
      Spec.map (CommRingCat.ofHom (chartCoefficientMap φ I J hIJ j)) = a :=
  (isPullback_projectiveCoefficientMap_chart φ I J hIJ j).lift_fst a k h

@[reassoc]
theorem serreActualCoefficientChartLift_toProjective :
    serreActualCoefficientChartLift φ I J hIJ j a k h ≫ chartι J j = k :=
  (isPullback_projectiveCoefficientMap_chart φ I J hIJ j).lift_snd a k h

theorem serreActualCoefficientChartLift_coordinate (i : σ) :
    affineFunctionHom a (chartCoordinate I j i) =
      affineFunctionHom (serreActualCoefficientChartLift φ I J hIJ j a k h)
        (chartCoordinate J j i) := by
  have hs := congrArg affineFunctionHom
    (serreActualCoefficientChartLift_toChart φ I J hIJ j a k h)
  rw [affineFunctionHom_comp_Spec] at hs
  rw [← hs]
  exact congrArg (affineFunctionHom
    (serreActualCoefficientChartLift φ I J hIJ j a k h))
      (chartCoefficientMap_coordinate φ I J hIJ j i)

theorem serreActualCoefficientChartLift_baseMap :
    (affineFunctionHom (serreActualCoefficientChartLift φ I J hIJ j a k h)).comp
        (chartBaseMap J j) = affineFunctionHom (k ≫ toBase J) := by
  have hs := congrArg (fun g => affineFunctionHom (g ≫ toBase J))
    (serreActualCoefficientChartLift_toProjective φ I J hIJ j a k h)
  rw [Category.assoc, chartι_toBase, affineFunctionHom_comp_Spec] at hs
  exact hs

end PfaffianDescent
