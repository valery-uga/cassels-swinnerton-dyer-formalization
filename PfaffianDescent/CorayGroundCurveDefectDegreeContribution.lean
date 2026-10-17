import PfaffianDescent.CorayActualResidueDegreeWeight
import PfaffianDescent.CorayGroundProjectiveCurveLocalDefect

/-!
# Genuine point-degree contribution of the original ground curve defect

The original K-curve stalk's own residue field is identified by an actual
constructed algebra equivalence with M. Actual finite normalization and the
conductor/Artinian argument give actual finite local defect length. Actual
ground dimension is that length times [M:K], hence at least [M:K].

This is the literal local contribution needed for Coray's genus correction,
not a global genus or Riemann-Roch assertion. Integral branch only.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open AlgebraicGeometry MvPolynomial TrivSqZeroExt IsLocalRing Module
open AllCharacteristics.HomogeneousProjective

universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ORIGINAL ground defect is finite over K, with its actual
point-degree weight and the actual lower bound needed for the later genus
argument. All local length/residue/normalization prerequisites are constructed
internally from original smooth cubic/selected equation/residue-point jets. -/
theorem groundSelectedCurve_ORIGINAL_point_normalizationDefect_degree_weight
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
    let phi := (groundNormalizedCurvePointJet p q anchor x hx pivot hp hpivot hq).toRingHom
    let hphi : Function.Surjective phi :=
      groundNormalizedCurvePointJet_surjective p q anchor x hx pivot hp hpivot hq heval
    let P := RingHom.ker (fullJetResidueMap phi)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
    let delta := localNormalizationDefect (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P))
    Module.Finite K delta ∧
      finrank K delta = (Module.length (Localization.AtPrime P) delta).toNat * finrank K M ∧
      finrank K M ≤ finrank K delta := by
  let phi := (groundNormalizedCurvePointJet p q anchor x hx pivot hp hpivot hq).toRingHom
  let hphi : Function.Surjective phi :=
    groundNormalizedCurvePointJet_surjective p q anchor x hx pivot hp hpivot hq heval
  let P := RingHom.ker (fullJetResidueMap phi)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
  let delta := localNormalizationDefect (Localization.AtPrime P)
    (FractionRing (Localization.AtPrime P))
  have hlength : 0 < Module.length (Localization.AtPrime P) delta ∧
      Module.length (Localization.AtPrime P) delta ≠ ⊤ :=
    groundSelectedCurve_ORIGINAL_point_normalizationDefect_length_pos_and_ne_top
      p q hphom hp0 n hqhom hnot anchor x hx pivot hp hpivot hq heval
  have hfiniteLength : IsFiniteLength (Localization.AtPrime P) delta :=
    Module.length_ne_top_iff.mp hlength.2
  let jet : Localization.AtPrime P →ₐ[K] CubicSurfaceFirstJet M :=
    fullJetAtActualPointAlgHom (groundNormalizedCurvePointJet p q anchor x hx pivot hp hpivot hq)
      hphi
  have hjet : Function.Surjective jet := fullJetAtActualPoint_surjective phi hphi
  letI : Module.Finite K (ResidueField (Localization.AtPrime P)) :=
    localFullJet_residue_finite jet hjet
  have hgroundFinite : Module.Finite K delta :=
    localModule_finite_over_ground_of_finiteLength hfiniteLength
  have hweight : finrank K delta =
      (Module.length (Localization.AtPrime P) delta).toNat * finrank K M :=
    localFullJet_ground_finrank_eq_presented_degree jet hjet hfiniteLength
  have hlower : 1 ≤ (Module.length (Localization.AtPrime P) delta).toNat :=
    ENat.toNat_pos (ne_of_gt hlength.1) hlength.2
  refine ⟨hgroundFinite, hweight, ?_⟩
  calc
    finrank K M = 1 * finrank K M := (one_mul _).symm
    _ ≤ (Module.length (Localization.AtPrime P) delta).toNat * finrank K M :=
      Nat.mul_le_mul_right _ hlower
    _ = finrank K delta := hweight.symm

end PfaffianDescent.Coray
