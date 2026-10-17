import PfaffianDescent.ActualRelativeDifferentialSection
import PfaffianDescent.ActualAffineDifferentialComparisonBasisAction
import PfaffianDescent.ActualAffineDifferentialSheafComparisonIso

/- SOURCE ONLY / UNVERIFIED. The genuine affine Ω comparison sends actual
universal differential sections to their canonical tilde localization. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

lemma actualAffineDifferentialSheafIso_section_D
    (f r : R) :
    (actualAffineDifferentialSheafIso (k := k) (R := R)).hom.val.app
      (op (PrimeSpectrum.basicOpen f))
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) (PrimeSpectrum.basicOpen f)
        (algebraMap R Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f) r)) =
      (tilde.toOpen (ModuleCat.of R (KaehlerDifferential k R))
        (PrimeSpectrum.basicOpen f)) (KaehlerDifferential.D k R r) := by
  let X := Spec (CommRingCat.of R)
  let P := schemeRelativeDifferentialsPresheaf (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let a := actualAffineDifferentialPresheafToTilde (k := k) (R := R)
  have h : adj.unit.app P ≫ (adj.right.map ((actualAffineDifferentialSheafIso
      (k := k) (R := R)).hom)) = a := by
    have ha := adj.homEquiv P (affineKaehlerModuleSheaf (k := k) (R := R)).apply_symm_apply a
    rw [Adjunction.homEquiv_unit] at ha
    exact ha
  have hx := congrArg (fun b => b.app (op (PrimeSpectrum.basicOpen f))
    ((schemeRelativeDifferentialsPresheafDerivation
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))).d
        (algebraMap R Γ(X, PrimeSpectrum.basicOpen f) r))) h
  change _ = a.app _ _ at hx
  rw [actualAffineDifferentialPresheafToTilde_basic_apply,
    actualAffineDifferentialPresheafBasicOpenEquiv_d] at hx
  exact hx

end PfaffianDescent
