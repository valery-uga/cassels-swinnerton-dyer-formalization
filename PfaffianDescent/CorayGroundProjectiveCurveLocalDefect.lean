import PfaffianDescent.CorayGroundAffineCurveLocalDefect

/-!
# Actual selected homogeneous ground curve to its ORIGINAL ground stalk

Existing proved coefficient/coordinate transport joins the ORIGINAL ground
polynomial full jet to the original coordinate-one K-curve quotient. Actual
smooth cubic irreducibility and selected-equation ideal nonmembership give
its local dimension bound. The original ground full jet then gives actual
positive finite local normalization-defect composition length.

This uses only the primitive integral branch of the actual pair ideal.
Weighted global genus, reducible branches and full Coray 1/4/10 remain open.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open AlgebraicGeometry MvPolynomial TrivSqZeroExt IsLocalRing Module
open AllCharacteristics.HomogeneousProjective

universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Literal ORIGINAL ground affine evaluation is the original projective
coordinate evaluation when the actual anchor coordinate equals one. -/
theorem normalizedGroundAffineEquation_evaluation
    (q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) :
    (normalizedAffineEquation anchor q).eval₂ (algebraMap K M)
      (fun i => x (anchor.succAbove i)) = q.eval₂ (algebraMap K M) x := by
  rw [← MvPolynomial.eval_map, ← normalizedAffineEquation_coefficients_map]
  exact (AlgHom.congr_fun (normalizedAffineEquation_evaluation anchor x hx)
    (MvPolynomial.map (algebraMap K M) q)).trans (MvPolynomial.eval_map _ _ _)

/-- The actual ORIGINAL ground affine derivative is the retained actual
projective derivative, with no coordinate-comparison premise. -/
theorem normalizedGroundAffineEquation_partial_evaluation
    (p : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (i : Fin 3) :
    (pderiv i (normalizedAffineEquation anchor p)).eval₂ (algebraMap K M)
      (fun r => x (anchor.succAbove r)) =
        (pderiv (anchor.succAbove i) p).eval₂ (algebraMap K M) x := by
  rw [normalizedAffineEquation_partial]
  exact normalizedGroundAffineEquation_evaluation _ anchor x hx

/-- Actual ORIGINAL K-polynomial jet evaluation is the original normalized
homogeneous jet through the composite K -> M -> Jet(M) coefficient map. -/
theorem normalizedGroundAffineEquation_jet_evaluation
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3) :
    groundAffineSurfaceJetMap (normalizedAffineEquation anchor p)
        (fun r => x (anchor.succAbove r)) pivot (normalizedAffineEquation anchor q) =
      q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
        (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
          anchor x pivot) := by
  rw [groundAffineSurfaceJetMap_apply_map,
    ← normalizedAffineEquation_coefficients_map,
    ← normalizedAffineEquation_coefficients_map]
  exact (AlgHom.congr_fun (normalizedAffineEquation_jet_evaluation anchor x hx
    (MvPolynomial.map (algebraMap K M) p) pivot)
      (MvPolynomial.map (algebraMap K M) q)).trans
        (normalizedProjectiveJet_baseChange_evaluation (algebraMap K M) q
          (MvPolynomial.map (algebraMap K M) p) anchor x pivot)

/-- The literal ORIGINAL coordinate-one ground curve carries the actual
homogeneous ground full jet, via proved value/derivative/jet transport. -/
def groundNormalizedCurvePointJet
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
        anchor x pivot) = 0) :
    affineCurveRing (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q) →ₐ[K]
      CubicSurfaceFirstJet M := by
  apply groundAffineCurvePointJet _ _ (fun r => x (anchor.succAbove r)) pivot
  · exact (normalizedGroundAffineEquation_evaluation p anchor x hx).trans hp
  · rwa [normalizedGroundAffineEquation_partial_evaluation p anchor x hx pivot]
  · exact (normalizedGroundAffineEquation_jet_evaluation p q anchor x hx pivot).trans hq

/-- ORIGINAL ground-polynomial minpoly preimages give the actual ORIGINAL
coordinate-one ground curve jet surjectivity, with no jet certificate. -/
theorem groundNormalizedCurvePointJet_surjective
    [CharZero K] [FiniteDimensional K M]
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
        anchor x pivot) = 0)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M)
      (fun r => x (anchor.succAbove r)))) :
    Function.Surjective (groundNormalizedCurvePointJet p q anchor x hx pivot hp hpivot hq) := by
  unfold groundNormalizedCurvePointJet
  exact groundAffineCurvePointJet_surjective _ _ _ _ _ _ _ heval

/-- The selected ORIGINAL ground curve's actual point ideal pulls back to
the ORIGINAL residue-point evaluation kernel in K[three coordinates]. -/
theorem groundNormalizedCurve_actualPointIdeal_comap_mk
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
        anchor x pivot) = 0) :
    (RingHom.ker (fullJetResidueMap
      (groundNormalizedCurvePointJet p q anchor x hx pivot hp hpivot hq).toRingHom)).comap
        (Ideal.Quotient.mk (affineCurveIdeal
          (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q))) =
      RingHom.ker (MvPolynomial.eval₂Hom (algebraMap K M)
        (fun r => x (anchor.succAbove r))) := by
  unfold groundNormalizedCurvePointJet
  exact groundAffineCurve_actualPointIdeal_comap_mk _ _ _ _ _ _ _

/-- Actual homogeneous smooth cubic and selected ORIGINAL ground equation
supply the actual original ground stalk's cotangent rank, with no local rank
or projective/affine identification certificate. -/
theorem groundNormalizedCurve_actualPoint_cotangent_finrank_ge_two
    [CharZero K] [FiniteDimensional K M]
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
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
    2 ≤ finrank (ResidueField (Localization.AtPrime P))
      (CotangentSpace (Localization.AtPrime P)) := by
  exact fullJetAtActualPoint_cotangent_finrank_ge_two _
    (groundNormalizedCurvePointJet_surjective p q anchor x hx pivot hp hpivot hq heval)

/-- At the ORIGINAL ground curve point selected by actual homogeneous full
jets, actual normalization-defect composition length is positive and finite.
Smooth projective p and actual selected q derive affine irreducibility and
ideal nonmembership internally; actual finite normalization is also derived.
Only the primitive integral-branch predicate on the actual pair ideal remains. -/
theorem groundSelectedCurve_ORIGINAL_point_normalizationDefect_length_pos_and_ne_top
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
    0 < Module.length (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) ∧
      Module.length (Localization.AtPrime P)
        (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) ≠ ⊤ := by
  let phi := (groundNormalizedCurvePointJet p q anchor x hx pivot hp hpivot hq).toRingHom
  let hphi : Function.Surjective phi :=
    groundNormalizedCurvePointJet_surjective p q anchor x hx pivot hp hpivot hq heval
  let P := RingHom.ker (fullJetResidueMap phi)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
  have hpirr := normalizedAffineEquation_irreducible_of_smooth_cubic p hphom hp0 anchor
  have hnotaff := normalizedAffineEquation_not_mem_of_smooth_cubic
    p q hphom hp0 n hqhom hnot anchor
  letI : Ring.DimensionLEOne (Localization.AtPrime P) :=
    affineCurve_local_dimensionLEOne_of_prime _ _ hpirr hnotaff P
  have hnontrivial : Nontrivial (localNormalizationDefect (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P))) :=
    localNormalizationDefect_nontrivial_of_surjective_fullJet
      (FractionRing (Localization.AtPrime P))
      (fullJetAtActualPoint phi hphi) (fullJetAtActualPoint_surjective phi hphi)
  exact ⟨Module.length_pos_iff.mpr hnontrivial,
    affineCurve_point_normalizationDefect_length_ne_top_charZero _ _ hpirr hnotaff P⟩

end PfaffianDescent.Coray
