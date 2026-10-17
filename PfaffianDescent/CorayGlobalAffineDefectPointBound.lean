import PfaffianDescent.CorayNormalizationDefectLocalizationComparison
import PfaffianDescent.CorayFiniteGroundLocalization
import PfaffianDescent.CorayAffineGlobalNormalizationDefect
import PfaffianDescent.CorayGroundCurveDefectDegreeContribution

/-!
# A genuine residue degree lower bound for the global affine defect

The actual affine normalization quotient maps onto the actual local quotient:
this follows from the constructed localization comparison and finite ground
dimension, not from a supplied global/local comparison. The actual original
residue degree contribution then bounds the global affine defect dimension.

Integral branch; GLOBAL AFFINE scope only. Genus and Riemann–Roch remain open.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial TrivSqZeroExt IsLocalRing Module
open AllCharacteristics.HomogeneousProjective

/-- Actual finite ground dimension and actual normalization localization
construct a finite local quotient of no larger ground dimension. -/
theorem normalizationDefect_point_ground_finite_and_finrank_le
    (K A : Type*) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Module.Finite K (localNormalizationDefect A (FractionRing A))]
    (P : Ideal A) [P.IsPrime] :
    Module.Finite K (localNormalizationDefect (Localization.AtPrime P)
        (FractionRing (Localization.AtPrime P))) ∧
      finrank K (localNormalizationDefect (Localization.AtPrime P)
        (FractionRing (Localization.AtPrime P))) ≤
      finrank K (localNormalizationDefect A (FractionRing A)) := by
  let e := (normalizationDefectLocalizationEquiv A P).restrictScalars A
  let m := LocalizedModule.mkLinearMap P.primeCompl
    (localNormalizationDefect A (FractionRing A))
  let f := e.toLinearMap.comp m
  letI : IsLocalizedModule P.primeCompl f :=
    IsLocalizedModule.of_linearEquiv P.primeCompl m e
  exact groundFinite_localization_finite_and_finrank_le P.primeCompl f

universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual double point at the presented finite residue extension forces
at least its residue degree in the actual GLOBAL AFFINE normalization defect
of the original ground curve. All comparison, ground finiteness, singular
local contribution, and residue-field weight are proved internally. -/
theorem groundSelectedCurve_globalAffineNormalizationDefect_degree_ge_point
    [CharZero K] [FiniteDimensional K M]
    (p q : MvPolynomial (Fin 4) K) (hphom : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hphom)] (n : ℕ) (hqhom : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (anchor : Fin 4)
    [hcurve : (affineCurveIdeal
      (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)).IsPrime]
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
        anchor x pivot) = 0)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M)
      (fun r => x (anchor.succAbove r)))) :
    finrank K M ≤ finrank K (localNormalizationDefect
      (affineCurveRing (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q))
      (FractionRing (affineCurveRing
        (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)))) := by
  let A := affineCurveRing (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)
  letI : Module.Finite K (localNormalizationDefect A (FractionRing A)) :=
    groundSelectedCurve_globalAffineNormalizationDefect_finite_over_ground
      p q hphom hp0 n hqhom hnot anchor
  let phi := (groundNormalizedCurvePointJet p q anchor x hx pivot hp hpivot hq).toRingHom
  let hphi : Function.Surjective phi :=
    groundNormalizedCurvePointJet_surjective p q anchor x hx pivot hp hpivot hq heval
  let P := RingHom.ker (fullJetResidueMap phi)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
  have hpoint := groundSelectedCurve_ORIGINAL_point_normalizationDefect_degree_weight
    p q hphom hp0 n hqhom hnot anchor x hx pivot hp hpivot hq heval
  have hcomparison := normalizationDefect_point_ground_finite_and_finrank_le K A P
  exact hpoint.2.2.trans hcomparison.2

end PfaffianDescent.Coray
