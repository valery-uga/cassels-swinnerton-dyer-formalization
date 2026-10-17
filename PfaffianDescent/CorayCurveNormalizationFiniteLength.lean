import PfaffianDescent.CorayNormalizationDefectFiniteLength
import PfaffianDescent.CorayLocalizedCurveNormalization

/-!
# Genuine finite local defect of the actual selected curve

Actual finite normalization is derived internally from actual finite-type
characteristic-zero equations. Actual dimension at most one is derived from
actual smooth cubic irreducibility and selected-curve ideal nonmembership.
The actual conductor/torsion/Artinian argument then proves finite COMPOSITION
length. At the actual original full-jet point, that length is positive.

Integral/reducible geometry, weighted ground descent, global genus and RR
remain separate open work. STATUS: UNVERIFIED source only.
-/

noncomputable section
namespace PfaffianDescent.Coray

open AlgebraicGeometry Algebra Module MvPolynomial IsLocalRing
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual point normalization gives an actual nonzero conductor element.
The finite normalization prerequisite is constructed, not supplied. -/
theorem affineCurve_point_conductor_exists_nonzero_charZero
    {M : Type*} [Field M] [CharZero M]
    (p q : MvPolynomial (Fin 3) M) [hcurve : (affineCurveIdeal p q).IsPrime]
    (P : Ideal (affineCurveRing p q)) [P.IsPrime] :
    ∃ a : Localization.AtPrime P,
      a ∈ normalizationConductor (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) ∧
      a ≠ 0 := by
  letI := affineCurve_point_finiteNormalization_charZero p q P
  exact normalizationConductor_exists_nonzero_of_finiteNormalization _ _

/-- Actual finite COMPOSITION length at every point of the literal integral
intersection, with actual normalization and local dimension derived internally. -/
theorem affineCurve_point_normalizationDefect_isFiniteLength_charZero
    {M : Type*} [Field M] [CharZero M]
    (p q : MvPolynomial (Fin 3) M) (hp : Irreducible p)
    (hq : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)))
    [hcurve : (affineCurveIdeal p q).IsPrime]
    (P : Ideal (affineCurveRing p q)) [P.IsPrime] :
    IsFiniteLength (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) := by
  letI := affineCurve_point_finiteNormalization_charZero p q P
  letI : Ring.DimensionLEOne (Localization.AtPrime P) :=
    affineCurve_local_dimensionLEOne_of_prime p q hp hq P
  exact localNormalizationDefect_isFiniteLength_of_finiteNormalization _ _

theorem affineCurve_point_normalizationDefect_length_ne_top_charZero
    {M : Type*} [Field M] [CharZero M]
    (p q : MvPolynomial (Fin 3) M) (hp : Irreducible p)
    (hq : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)))
    [hcurve : (affineCurveIdeal p q).IsPrime]
    (P : Ideal (affineCurveRing p q)) [P.IsPrime] :
    Module.length (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr
    (affineCurve_point_normalizationDefect_isFiniteLength_charZero p q hp hq P)

/-- Actual ground equations and an actual residue field give finite local
defect length without any finite-normalization or local-dimension premise. -/
theorem groundSelectedCurve_point_normalizationDefect_isFiniteLength_charZero
    {K M : Type u} [Field K] [CharZero K] [Field M] [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hqhom : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (anchor : Fin 4)
    [hcurve : (affineCurveIdeal
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q))).IsPrime]
    (P : Ideal (affineCurveRing
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q)))) [P.IsPrime] :
    IsFiniteLength (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) := by
  letI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  exact affineCurve_point_normalizationDefect_isFiniteLength_charZero _ _
    (groundSmoothCubic_residueAffineEquation_irreducible (M := M) p hp hp0 anchor)
    (groundSelectedCurve_residueAffineEquation_not_mem (M := M) p q hp hp0 n hqhom hnot anchor) P

/-- The genuine local defect's actual ENat length is finite. -/
theorem groundSelectedCurve_point_normalizationDefect_length_ne_top_charZero
    {K M : Type u} [Field K] [CharZero K] [Field M] [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hqhom : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (anchor : Fin 4)
    [hcurve : (affineCurveIdeal
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q))).IsPrime]
    (P : Ideal (affineCurveRing
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q)))) [P.IsPrime] :
    Module.length (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr
    (groundSelectedCurve_point_normalizationDefect_isFiniteLength_charZero
      p q hp hp0 n hqhom hnot anchor P)

/-- At the actual original full-jet residue point, the literal curve defect
has POSITIVE FINITE actual composition length. This is a local integral-branch
result, not an assumed or proved weighted global genus statement. -/
theorem groundSelectedCurve_actualResiduePoint_normalizationDefect_length_pos_and_ne_top
    {K M : Type u} [Field K] [CharZero K] [Field M] [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hqhom : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (anchor : Fin 4)
    [hcurve : (affineCurveIdeal
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q))).IsPrime]
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hpx : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
        anchor x pivot) = 0) :
    let φ := (groundCurvePointJet p q anchor x hx pivot hpx hpivot hq).toRingHom
    let hφ : Function.Surjective φ := groundCurvePointJet_surjective p q anchor x hx pivot hpx hpivot hq
    let P := RingHom.ker (fullJetResidueMap φ)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
    0 < Module.length (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) ∧
      Module.length (Localization.AtPrime P)
        (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) ≠ ⊤ := by
  let φ := (groundCurvePointJet p q anchor x hx pivot hpx hpivot hq).toRingHom
  let hφ : Function.Surjective φ := groundCurvePointJet_surjective p q anchor x hx pivot hpx hpivot hq
  let P := RingHom.ker (fullJetResidueMap φ)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
  have hnontrivial : Nontrivial (localNormalizationDefect (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P))) :=
    groundSelectedCurve_actualResiduePoint_normalizationDefect_nontrivial
      p q hp hp0 n hqhom hnot anchor x hx pivot hpx hpivot hq
  exact ⟨Module.length_pos_iff.mpr hnontrivial,
    groundSelectedCurve_point_normalizationDefect_length_ne_top_charZero
      p q hp hp0 n hqhom hnot anchor P⟩

end PfaffianDescent.Coray
