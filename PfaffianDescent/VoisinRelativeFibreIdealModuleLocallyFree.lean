import PfaffianDescent.VoisinRelativeFibreCartier
import PfaffianDescent.ClosedImmersionIdealModuleLocallyFree

/-! The actual ideal module of each canonical local Voisin fibre is locally free. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For every local-ring-valued point of the nontrivial moving-equation
space, the actual pulled-back relative zero-locus ideal module is locally
free of rank one. -/
theorem flatGradedNontrivialOpen_localSchemePoint_relativeFibre_idealModule_isLocallyFree
    {K R T : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0) :
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    let fibreMap := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h n
    letI : IsClosedImmersion fibreMap :=
      flatGradedNontrivialOpen_localSchemePoint_relativeFibre_isClosedImmersion
        J r q e hRank a ha ha0 n
    (IdealSheafDataModule.closedImmersionModule fibreMap).IsLocallyFree := by
  dsimp only
  letI : IsClosedImmersion (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha _ _ _) :=
    flatGradedNontrivialOpen_localSchemePoint_relativeFibre_isClosedImmersion
      J r q e hRank a ha ha0 n
  exact (flatGradedNontrivialOpen_localSchemePoint_relativeFibre_regularPrincipalImmersion
    J r q e hRank a ha ha0 n).closedImmersionModule_isLocallyFree

/-- The actual ideal module of the canonical local relative fibre of
Voisin's moving-equation family is locally free of rank one. -/
theorem flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_idealModule_isLocallyFree
    {K R : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (y : flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0) :
    let E := flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0
    let k : E ⟶ Spec (.of K) :=
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    let h : E ⟶ projectiveParameters K (Fin 4) 3 :=
      flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
    let fibreMap := fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha k h (E.fromSpecStalk y)
    letI : IsClosedImmersion fibreMap :=
      flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_isClosedImmersion
        J r q e hRank a ha ha0 y
    (IdealSheafDataModule.closedImmersionModule fibreMap).IsLocallyFree := by
  dsimp only
  letI : IsClosedImmersion (fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
      a ha _ _ _) :=
    flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_isClosedImmersion
      J r q e hRank a ha ha0 y
  exact (flatGradedNontrivialOpen_stalkBaseChange_relativeFibre_regularPrincipalImmersion
    J r q e hRank a ha ha0 y).closedImmersionModule_isLocallyFree

end PfaffianDescent
