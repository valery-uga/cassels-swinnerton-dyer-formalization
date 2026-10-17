import PfaffianDescent.CorayActualPositiveRestrictedWholeMatrix
import PfaffianDescent.VoisinGenericPullbackCoordinates
import AllCharacteristics.AmbientChartPresentation

/-! The actual basicOpenIsoSpec coefficient comparison. The original
normalized chart coefficient and canonical Gamma-Spec ring isomorphism
are retained, rather than supplying an abstract coefficient identification.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open ProjectiveNegativeTwist BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

private lemma actualAmbientChartCoefficientSection_self
    (j : Fin 4) (p : MvPolynomial (Fin 4) K) :
    actualAmbientChartCoefficientSection j (Proj.basicOpen PS (X j)) le_rfl p =
      Proj.awayToSection PS (X j) (ambientChartEvaluation j p) := by
  change (Proj PS).presheaf.map (𝟙 (op (Proj.basicOpen PS (X j))))
    (Proj.awayToSection PS (X j) (ambientChartEvaluation j p)) = _
  have hid := CategoryTheory.Functor.map_id (Proj PS).presheaf
    (op (Proj.basicOpen PS (X j)))
  exact ConcreteCategory.congr_hom hid
    (Proj.awayToSection PS (X j) (ambientChartEvaluation j p))

/-- The exact normalized coefficient transported by the ACTUAL inverse
basic-open/Spec isomorphism is the canonical Gamma-Spec image of that SAME
native chart-ring element. No coefficient equality is supplied as a premise. -/
theorem actualBasicOpenIsoSpec_inv_normalizedCoefficient
    (j : Fin 4) (p : MvPolynomial (Fin 4) K) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    e.inv.appTop.hom
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U le_rfl p)) =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).inv.hom
        (ambientChartEvaluation j p) := by
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let B := HomogeneousLocalization.Away PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let gamma := Scheme.ΓSpecIso (CommRingCat.of B)
  let c := ambientChartEvaluation j p
  let v := gamma.inv.hom c
  have hehom : e.hom.appTop = gamma.hom ≫ Proj.awayToSection PS (X j) ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top PS (X j)
  have hgamma : gamma.hom.hom v = c :=
    ConcreteCategory.congr_hom gamma.inv_hom_id c
  have hbeta := congrArg (fun f : Γ(Spec (CommRingCat.of B), ⊤) ⟶ Γ((U : Scheme), ⊤) =>
    f.hom v) hehom
  change e.hom.appTop.hom v =
    U.topIso.inv.hom (Proj.awayToSection PS (X j) (gamma.hom.hom v)) at hbeta
  have hbeta' : e.hom.appTop.hom v = U.topIso.inv.hom (Proj.awayToSection PS (X j) c) :=
    hbeta.trans (congrArg (fun z : B => U.topIso.inv.hom
      (Proj.awayToSection PS (X j) z)) hgamma)
  have heinv := congrArg (fun f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B) =>
    f.appTop) e.inv_hom_id
  change e.hom.appTop ≫ e.inv.appTop = 𝟙 Γ(Spec (CommRingCat.of B), ⊤) at heinv
  have hcoef := actualAmbientChartCoefficientSection_self j p
  calc
    _ = e.inv.appTop.hom (U.topIso.inv.hom (Proj.awayToSection PS (X j) c)) :=
      congrArg (fun z => e.inv.appTop.hom (U.topIso.inv.hom z)) hcoef
    _ = e.inv.appTop.hom (e.hom.appTop.hom v) :=
      congrArg (fun z => e.inv.appTop.hom z) hbeta'.symm
    _ = v := ConcreteCategory.congr_hom heinv v

/-- Actual canonical unit pullback carries the normalized open-chart
endomorphism to multiplication by the canonical Gamma-Spec image of the
original normalized chart coefficient. -/
theorem actualBasicOpenIsoSpec_pullback_normalizedUnitEndomorphism
    (j : Fin 4) (p : MvPolynomial (Fin 4) K) :
    let U := Proj.basicOpen PS (X j)
    let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    pullbackUnitEndomorphism e.inv (isIso_pullbackUnitComparison e.inv)
      (unitEndomorphismOfRegularFunction
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U le_rfl p))) =
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).inv.hom
          (ambientChartEvaluation j p)) := by
  dsimp only
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let c := U.topIso.inv.hom (actualAmbientChartCoefficientSection j U le_rfl p)
  have h := pullbackUnitEndomorphismOfRegularFunction_eq_appTop_general
    e.inv (isIso_pullbackUnitComparison e.inv) c
  exact h.trans (congrArg (unitEndomorphismOfRegularFunction
    (X := Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))))
      (actualBasicOpenIsoSpec_inv_normalizedCoefficient j p))

end PfaffianDescent.Coray
