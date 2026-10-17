import PfaffianDescent.LocalizationPrincipalOpen294
import PfaffianDescent.MonomialChartOverlapLocalization292
import PfaffianDescent.PolynomialWholeIdealScalarExtension286

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (hk : B k = 0)

/-- The native292 coefficient localization embeds in its original cyclic coefficient affine scheme. -/
def monomialOverlapPrincipalOpenMap294 :=
  localizationPrincipalOpenMap294 (universalMonomialOverlapDet292 R m n B C k hk)

lemma monomialOverlapPrincipalOpenMap_isOpenImmersion294 :
    IsOpenImmersion (monomialOverlapPrincipalOpenMap294 R m n B C k hk) :=
  localizationPrincipalOpenMap_isOpenImmersion294 (universalMonomialOverlapDet292 R m n B C k hk)

lemma monomialOverlapPrincipalOpenMap_range294 :
    Set.range (monomialOverlapPrincipalOpenMap294 R m n B C k hk) =
      (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B C k hk) :
        Set (PrimeSpectrum (UniversalCyclicCoefficientAlgebra282 R m n B k))) :=
  localizationPrincipalOpenMap_range294 (universalMonomialOverlapDet292 R m n B C k hk)

/-- A genuine Scheme isomorphism to the determinant principal open of the original coefficient chart. -/
def monomialOverlapPrincipalOpenIso294 :=
  localizationPrincipalOpenIso294 (universalMonomialOverlapDet292 R m n B C k hk)

lemma monomialOverlapPrincipalOpenIso_hom_fac294 :
    (monomialOverlapPrincipalOpenIso294 R m n B C k hk).hom ≫
        Scheme.Opens.ι (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B k)))
          (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B C k hk)) =
      monomialOverlapPrincipalOpenMap294 R m n B C k hk :=
  localizationPrincipalOpenIso_hom_fac294 (universalMonomialOverlapDet292 R m n B C k hk)

/-- Extend the same literal original whole universal ideal along the actual coefficient localization. -/
def monomialOverlapWholeIdeal294 :=
  (universalCyclicWholeAmbientIdeal282 R m n B k).map
    (MvPolynomial.map (algebraMap (UniversalCyclicCoefficientAlgebra282 R m n B k)
      (MonomialOverlapCoefficientAlgebra292 R m n B C k hk)))

/-- This is the genuine whole-quotient scalar extension equivalence; no reduced-support replacement. -/
def monomialOverlapWholeQuotientScalarEquiv294 :=
  polynomialWholeIdealScalarExtension286
    (R := UniversalCyclicCoefficientAlgebra282 R m n B k) (σ := Fin m)
    (MonomialOverlapCoefficientAlgebra292 R m n B C k hk)
    (universalCyclicWholeAmbientIdeal282 R m n B k)

end PfaffianDescent
