import PfaffianDescent.CorayCoefficientRetractionDescent
import PfaffianDescent.CoraySmoothNormalizedCurveBridge
import AllCharacteristics.ProjectiveFiberSmoothness

/-!
# Ground selected curve to its actual residue-field local defect

Actual coefficient retraction descends polynomial divisibility, so the chosen
ground equation remains outside the actual extension-field surface ideal.
Smoothness of the actual base-changed projective cubic is proved by the actual
projective base-change theorem. Ground full-jet vanishing then constructs the
actual residue-field curve jet and its actual point localization.

The integral branch retains only the primitive prime predicate on the actual
two-equation ideal. Global/reducible curve geometry, finite defect, residue-
weighted genus and Riemann-Roch are still open.

STATUS: UNVERIFIED source only. Root alone runs compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open AlgebraicGeometry MvPolynomial TrivSqZeroExt IsLocalRing Module
open AllCharacteristics.HomogeneousProjective

universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ground smooth cubic has an irreducible actual normalized
residue-field equation, using actual smooth projective base change. -/
theorem groundSmoothCubic_residueAffineEquation_irreducible
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (anchor : Fin 4) :
    Irreducible (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p)) := by
  letI : Smooth (hypersurfaceToBase (MvPolynomial.map (algebraMap K M) p)
      (hp.map (algebraMap K M))) := smooth_hypersurfaceToBase_map (algebraMap K M) p hp
  have hpM0 : MvPolynomial.map (algebraMap K M) p ≠ 0 := by
    intro hzero
    apply hp0
    exact MvPolynomial.map_injective (algebraMap K M) (algebraMap K M).injective
      (by simpa only [map_zero] using hzero)
  exact normalizedAffineEquation_irreducible_of_smooth_cubic
    (MvPolynomial.map (algebraMap K M) p) (hp.map (algebraMap K M)) hpM0 anchor

/-- Genuine ground ideal nonmembership survives the actual residue-field
coefficient extension and the actual normalized affine chart. -/
theorem groundSelectedCurve_residueAffineEquation_not_mem
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (anchor : Fin 4) :
    normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q) ∉
      Ideal.span ({normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p)} :
        Set (MvPolynomial (Fin 3) M)) := by
  letI : Smooth (hypersurfaceToBase (MvPolynomial.map (algebraMap K M) p)
      (hp.map (algebraMap K M))) := smooth_hypersurfaceToBase_map (algebraMap K M) p hp
  have hpM0 : MvPolynomial.map (algebraMap K M) p ≠ 0 := by
    intro hzero
    apply hp0
    exact MvPolynomial.map_injective (algebraMap K M) (algebraMap K M).injective
      (by simpa only [map_zero] using hzero)
  exact normalizedAffineEquation_not_mem_of_smooth_cubic
    (MvPolynomial.map (algebraMap K M) p) (MvPolynomial.map (algebraMap K M) q)
    (hp.map (algebraMap K M)) hpM0 n (hq.map (algebraMap K M))
    (groundPolynomial_map_not_mem_span (M := M) p q hnot) anchor

/-- The selected actual residue-field affine curve has dimension at most
one, regardless of its integral/reducible/nonreduced branch. -/
theorem groundSelectedCurve_residueAffineCurve_ringKrullDim_le_one
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (anchor : Fin 4) :
    ringKrullDim (affineCurveRing
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q))) ≤ 1 :=
  affineCurve_ringKrullDim_le_one _ _
    (groundSmoothCubic_residueAffineEquation_irreducible (M := M) p hp hp0 anchor)
    (groundSelectedCurve_residueAffineEquation_not_mem (M := M) p q hp hp0 n hq hnot anchor)

/-- Actual ground jet evaluation constructs an actual quotient jet over the
actual residue field; all coordinate and derivative transport is proved. -/
def groundCurvePointJet
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
        anchor x pivot) = 0) :
    affineCurveRing
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) p))
      (normalizedAffineEquation anchor (MvPolynomial.map (algebraMap K M) q)) →ₐ[M]
      CubicSurfaceFirstJet M := by
  let pM := MvPolynomial.map (algebraMap K M) p
  let qM := MvPolynomial.map (algebraMap K M) q
  have hpM : eval x pM = 0 := by
    simpa only [pM, MvPolynomial.eval_map] using hp
  have hpivotM : eval x (pderiv (anchor.succAbove pivot) pM) ≠ 0 := by
    simpa only [pM, MvPolynomial.pderiv_map, MvPolynomial.eval_map] using hpivot
  have hjetM : aeval (R := M) (cubicNormalizedSurfacePoint_tangentJet pM anchor x pivot) qM = 0 :=
    (normalizedProjectiveJet_baseChange_evaluation (algebraMap K M) q pM anchor x pivot).trans hq
  have hvalue : eval (fun i => x (anchor.succAbove i)) (normalizedAffineEquation anchor pM) = 0 :=
    (AlgHom.congr_fun (normalizedAffineEquation_evaluation anchor x hx) pM).trans hpM
  have hpartial : eval (fun i => x (anchor.succAbove i))
      (pderiv pivot (normalizedAffineEquation anchor pM)) ≠ 0 := by
    rwa [normalizedAffineEquation_partial_evaluation anchor x hx]
  have hjet : affineNormalizedSurfaceJetMap (normalizedAffineEquation anchor pM)
      (fun i => x (anchor.succAbove i)) pivot (normalizedAffineEquation anchor qM) = 0 :=
    (AlgHom.congr_fun (normalizedAffineEquation_jet_evaluation anchor x hx pM pivot) qM).trans hjetM
  exact affineCurvePointJet (normalizedAffineEquation anchor pM) (normalizedAffineEquation anchor qM)
    (fun i => x (anchor.succAbove i)) pivot hvalue hpartial hjet

/-- Explicit ambient preimages give the actual ground-constructed curve jet
surjectivity. No quotient-jet surjectivity certificate is an input. -/
theorem groundCurvePointJet_surjective
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
        anchor x pivot) = 0) :
    Function.Surjective (groundCurvePointJet p q anchor x hx pivot hp hpivot hq) := by
  unfold groundCurvePointJet
  exact affineCurvePointJet_surjective _ _ _ _ _ _ _

/-- Actual local cotangent rank at the original residue-field point of the
actual curve constructed from ground equations. -/
theorem groundCurve_actualResiduePoint_cotangent_finrank_ge_two
    (p q : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (CubicSurfaceFirstJet M)).comp (algebraMap K M))
      (cubicNormalizedSurfacePoint_tangentJet (MvPolynomial.map (algebraMap K M) p)
        anchor x pivot) = 0) :
    let φ := (groundCurvePointJet p q anchor x hx pivot hp hpivot hq).toRingHom
    let hφ : Function.Surjective φ := groundCurvePointJet_surjective p q anchor x hx pivot hp hpivot hq
    let P := RingHom.ker (fullJetResidueMap φ)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
    2 ≤ finrank (ResidueField (Localization.AtPrime P))
      (CotangentSpace (Localization.AtPrime P)) := by
  exact fullJetAtActualPoint_cotangent_finrank_ge_two _
    (groundCurvePointJet_surjective p q anchor x hx pivot hp hpivot hq)

/-- Ground smooth p and actual selected q give a genuine literal residue-
field curve normalization defect on its primitive integral branch. -/
theorem groundSelectedCurve_actualResiduePoint_normalizationDefect_nontrivial
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
    Nontrivial (localNormalizationDefect (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P))) := by
  let φ := (groundCurvePointJet p q anchor x hx pivot hpx hpivot hq).toRingHom
  let hφ : Function.Surjective φ := groundCurvePointJet_surjective p q anchor x hx pivot hpx hpivot hq
  let P := RingHom.ker (fullJetResidueMap φ)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
  letI : Ring.DimensionLEOne (Localization.AtPrime P) :=
    affineCurve_local_dimensionLEOne_of_prime _ _
      (groundSmoothCubic_residueAffineEquation_irreducible (M := M) p hp hp0 anchor)
      (groundSelectedCurve_residueAffineEquation_not_mem (M := M) p q hp hp0 n hqhom hnot anchor) P
  exact localNormalizationDefect_nontrivial_of_surjective_fullJet
    (FractionRing (Localization.AtPrime P))
    (fullJetAtActualPoint φ hφ) (fullJetAtActualPoint_surjective φ hφ)

end PfaffianDescent.Coray
