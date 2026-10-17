import PfaffianDescent.SurjectiveAffineActualIdealTildeIso
import PfaffianDescent.NativeCanonicalIdealInclusionFactory013
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernel

/- Source-only013. Canonical Iso and inclusion law are coupled upstream;
no raw/closed image square joins or specialized Hom-chain joins remain. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualClosedImmersionModuleEqIso_toUnit
    {X Z : Scheme.{u}} (f g : Z ⟶ X) (h : f = g) :
    (eqToIso (congrArg closedImmersionModule h)).hom ≫
      closedImmersionModuleToUnit g = closedImmersionModuleToUnit f := by
  cases h
  simp

/-- The SAME original SourceIso inverse/unit diagram, returned in the checked
producer's inferred object parameters. No concrete category header is re-elaborated. -/
def actualClosedImmersionSourceIso_inv_toUnit :=
  @nativeClosedImmersionSourceInverseRawSquare013

lemma surjectiveAffineActualIdealTildeIso_hom_toUnit
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    (surjectiveAffineActualIdealTildeIso rho hrho).hom ≫
      closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom rho)) =
    (tilde.functor (.of R)).map (ModuleCat.ofHom (RingHom.ker rho).subtype) ≫
      (affineGlobalSectionsUnitTildeIso (A := R)).hom := by
  exact surjectiveAffineActualIdealTildeData_hom_toUnit013 rho hrho

lemma surjectiveAffineActualIdealTildeIso_eq_native
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    surjectiveAffineActualIdealTildeIso rho hrho =
      cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso rho := by
  dsimp only
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  let j := Spec.map (CommRingCat.ofHom rho)
  letI : Mono (closedImmersionModuleToUnit j) := by
    change Mono (idealModuleToUnit _)
    infer_instance
  apply Iso.ext
  apply (cancel_mono (closedImmersionModuleToUnit j)).1
  exact (surjectiveAffineActualIdealTildeIso_hom_toUnit rho hrho).trans
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso_hom_toUnit rho).symm


end PfaffianDescent
