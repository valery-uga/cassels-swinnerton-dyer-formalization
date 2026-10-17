import PfaffianDescent.CorayAffineCurveDimension
import PfaffianDescent.CorayNormalizedProjectiveJetTransport
import PfaffianDescent.CoraySmoothCurveHilbert
import PfaffianDescent.VoisinSmoothCubicChartDomain
import PfaffianDescent.DehomogenizedQuadricsRelativePrime
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual smooth projective cubic to the actual affine curve defect

The Fin3 equation is identified with the existing actual eliminated chart
presentation by an explicit variable equivalence. Smoothness makes the chart
an actual domain, hence its actual principal defining equation irreducible.
The selected homogeneous q remains outside the affine surface ideal by actual
homogeneous relative-primality transport. No affine irreducibility or
nonmembership certificate is assumed.

The final local normalization statement applies to the integral-curve branch,
expressed by the primitive prime predicate on the literal affine pair ideal.
Residue-degree base-change descent, reducible branches and global genus/RR
remain open. STATUS: UNVERIFIED source only; root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open AlgebraicGeometry MvPolynomial TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective

universe u
variable {M : Type u} [Field M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The explicit Fin3 elimination is the existing actual coordinate-one
elimination after the literal retained-variable equivalence. -/
theorem normalizedAffineEquation_rename_retained
    (anchor : Fin 4) (p : MvPolynomial (Fin 4) M) :
    (MvPolynomial.renameEquiv M (finSuccAboveEquiv anchor))
        (normalizedAffineEquation anchor p) = coordinateOneEvaluation anchor p := by
  classical
  have hcomp : (MvPolynomial.renameEquiv M (finSuccAboveEquiv anchor)).toAlgHom.comp
      (normalizedAffineEquation (M := M) anchor) = coordinateOneEvaluation anchor := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = anchor
    · subst j
      simp [normalizedAffineEquation, coordinateOneEvaluation]
    · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hj
      simp [normalizedAffineEquation, coordinateOneEvaluation,
        Fin.succAbove_ne, finSuccAboveEquiv_apply, MvPolynomial.renameEquiv_apply]
  exact AlgHom.congr_fun hcomp p

/-- Smoothness forces the actual equation of each actual eliminated chart
to be irreducible, from the actual chart domain and actual kernel theorem. -/
theorem coordinateOneEquation_irreducible_of_smooth_cubic
    (p : MvPolynomial (Fin 4) M) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (anchor : Fin 4) :
    Irreducible (coordinateOneEvaluation anchor p) := by
  let I := equationIdeal p hp
  letI : Algebra M (ChartRing I anchor) := (chartBaseMap I anchor).toAlgebra
  letI : IsDomain (ChartRing I anchor) := smoothCubic_chartRing_isDomain p hp hp0 anchor
  let e : MvPolynomial {i : Fin 4 // i ≠ anchor} M →ₐ[M] ChartRing I anchor :=
    aeval (fun i => chartCoordinate I anchor i.1)
  obtain ⟨_, hker, hnonzero⟩ :=
    smoothCubic_eliminatedChartMap_surjective_and_kernel p hp hp0 anchor
  have hprime : (Ideal.span ({coordinateOneEvaluation anchor p} :
      Set (MvPolynomial {i : Fin 4 // i ≠ anchor} M))).IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime e.toRingHom
  exact ((Ideal.span_singleton_prime hnonzero).mp hprime).irreducible

/-- The actual Fin3 surface equation is irreducible, without a supplied
irreducibility certificate for its affine chart. -/
theorem normalizedAffineEquation_irreducible_of_smooth_cubic
    (p : MvPolynomial (Fin 4) M) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (anchor : Fin 4) :
    Irreducible (normalizedAffineEquation anchor p) := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv M
    (finSuccAboveEquiv anchor))).mp
  rw [normalizedAffineEquation_rename_retained]
  exact coordinateOneEquation_irreducible_of_smooth_cubic p hp hp0 anchor

/-- Actual homogeneous relative primality survives the explicit Fin3
coordinate-one map. The installed theorem proves the homogenization step. -/
theorem normalizedAffineEquations_isRelPrime_of_homogeneous_isRelPrime
    {p q : MvPolynomial (Fin 4) M} {n m : ℕ}
    (hp : p.IsHomogeneous n) (hq : q.IsHomogeneous m) (hn : 0 < n)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (anchor : Fin 4) :
    IsRelPrime (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q) := by
  apply IsRelPrime.of_map (MvPolynomial.renameEquiv M (finSuccAboveEquiv anchor))
  rw [normalizedAffineEquation_rename_retained, normalizedAffineEquation_rename_retained]
  exact QuarticNet.coordinateOneEvaluation_isRelPrime_of_homogeneous_isRelPrime
    hp hq hn hp0 hrel anchor

/-- A genuinely selected homogeneous q outside the cubic ideal stays outside
that cubic's actual affine ideal on every normalized chart. -/
theorem normalizedAffineEquation_not_mem_of_smooth_cubic
    (p q : MvPolynomial (Fin 4) M) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) M))) (anchor : Fin 4) :
    normalizedAffineEquation anchor q ∉
      Ideal.span ({normalizedAffineEquation anchor p} : Set (MvPolynomial (Fin 3) M)) := by
  have hirr := normalizedAffineEquation_irreducible_of_smooth_cubic p hp hp0 anchor
  have hrel := normalizedAffineEquations_isRelPrime_of_homogeneous_isRelPrime
    hp hq (by omega) hp0 (isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot) anchor
  intro hmem
  exact hirr.not_isUnit (hrel (dvd_refl _) (Ideal.mem_span_singleton.mp hmem))

/-- Every actual affine chart of the selected projective intersection has
Krull dimension at most one, including the reducible or nonreduced branches. -/
theorem normalizedProjectiveCurve_ringKrullDim_le_one
    (p q : MvPolynomial (Fin 4) M) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) M))) (anchor : Fin 4) :
    ringKrullDim (affineCurveRing (normalizedAffineEquation anchor p)
      (normalizedAffineEquation anchor q)) ≤ 1 :=
  affineCurve_ringKrullDim_le_one
    (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)
    (normalizedAffineEquation_irreducible_of_smooth_cubic p hp hp0 anchor)
    (normalizedAffineEquation_not_mem_of_smooth_cubic p q hp hp0 n hq hnot anchor)

/-- The original smooth projective cubic and literal selected homogeneous
full jet produce a genuine local normalization defect on the integral branch.
The local domain, dimension and cotangent conditions are all derived. -/
theorem normalizedProjectiveCurve_actualPoint_normalizationDefect_nontrivial
    (p q : MvPolynomial (Fin 4) M) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hqhom : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) M)))
    (anchor : Fin 4)
    [hcurve : (affineCurveIdeal (normalizedAffineEquation anchor p)
      (normalizedAffineEquation anchor q)).IsPrime]
    (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hpx : eval x p = 0)
    (hpivot : eval x (pderiv (anchor.succAbove pivot) p) ≠ 0)
    (hq : aeval (R := M) (cubicNormalizedSurfacePoint_tangentJet p anchor x pivot) q = 0) :
    let p' := normalizedAffineEquation anchor p
    let q' := normalizedAffineEquation anchor q
    let x' := fun i => x (anchor.succAbove i)
    let hpx' : eval x' p' = 0 :=
      (AlgHom.congr_fun (normalizedAffineEquation_evaluation anchor x hx) p).trans hpx
    let hpivot' : eval x' (pderiv pivot p') ≠ 0 := by
      rwa [normalizedAffineEquation_partial_evaluation anchor x hx]
    let hq' : affineNormalizedSurfaceJetMap p' x' pivot q' = 0 :=
      (AlgHom.congr_fun (normalizedAffineEquation_jet_evaluation anchor x hx p pivot) q).trans hq
    let φ := (affineCurvePointJet p' q' x' pivot hpx' hpivot' hq').toRingHom
    let hφ : Function.Surjective φ := affineCurvePointJet_surjective p' q' x' pivot hpx' hpivot' hq'
    let P := RingHom.ker (fullJetResidueMap φ)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
    Nontrivial (localNormalizationDefect (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P))) := by
  exact affineCurve_actualPoint_normalizationDefect_nontrivial
    (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)
    (normalizedAffineEquation_irreducible_of_smooth_cubic p hp hp0 anchor)
    (normalizedAffineEquation_not_mem_of_smooth_cubic p q hp hp0 n hqhom hnot anchor)
    (fun i => x (anchor.succAbove i)) pivot
    ((AlgHom.congr_fun (normalizedAffineEquation_evaluation anchor x hx) p).trans hpx)
    (by rwa [normalizedAffineEquation_partial_evaluation anchor x hx])
    ((AlgHom.congr_fun (normalizedAffineEquation_jet_evaluation anchor x hx p pivot) q).trans hq)

end PfaffianDescent.Coray
