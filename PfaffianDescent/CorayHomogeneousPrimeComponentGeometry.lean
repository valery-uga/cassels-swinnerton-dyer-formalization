import PfaffianDescent.CorayHomogeneousComponentOriginalClosedPoint
import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.Ideal.Height

/-!
# Native integrality and curve dimension of the actual minimal component

Prime quotient, the actual point, native homogeneous stalk localizations, and
the bottom homogeneous generic point derive IsIntegral of the component scheme.
Surjective quotient charts of the actual p/q intersection derive dimension <=1
for all component charts and OWN component stalks. No geometric integrality,
Galois orbit, component degree/genus, regularity, or H0-normalization constants
is assumed or asserted. SOURCE ONLY / UNVERIFIED. Root alone compiles/audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A prime homogeneous quotient with an actual projective point has a native
integral scheme. Nonemptiness rules out the irrelevant-bottom degeneration;
all reducedness and topological irreducibility are derived. -/
theorem homogeneousPrime_projectiveScheme_isIntegral
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    IsIntegral (scheme C) := by
  letI : IsDomain (CoordinateRing C) :=
    (Ideal.Quotient.isDomain_iff_prime C.toIdeal).mpr hprime
  let X := scheme C
  letI : Nonempty X := ⟨P⟩
  have hStalk (x : X) : IsDomain (X.presheaf.stalk x) := by
    let J := x.asHomogeneousIdeal.toIdeal
    letI : J.IsPrime := x.isPrime
    letI : IsDomain (Localization J.primeCompl) :=
      IsLocalization.isDomain_localization J.primeCompl_le_nonZeroDivisors
    letI : IsDomain (HomogeneousLocalization.AtPrime (grading C) J) :=
      (HomogeneousLocalization.val_injective J.primeCompl).isDomain
        (algebraMap (HomogeneousLocalization.AtPrime (grading C) J)
          (Localization J.primeCompl))
    let e : X.presheaf.stalk x ≃+*
        HomogeneousLocalization.AtPrime (grading C) J :=
      (Proj.stalkIso (grading C) x).commRingCatIsoToRingEquiv
    exact MulEquiv.isDomain (HomogeneousLocalization.AtPrime (grading C) J)
      e.toMulEquiv
  letI (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    letI := hStalk x
    infer_instance
  letI : IsReduced X := isReduced_of_isReduced_stalk X
  have hrel : ¬ HomogeneousIdeal.irrelevant (grading C) ≤
      (⊥ : HomogeneousIdeal (grading C)) := by
    intro h
    exact P.not_irrelevant_le (h.trans bot_le)
  let eta : ProjectiveSpectrum (grading C) :=
    ⟨⊥, by simpa using (Ideal.isPrime_bot (α := CoordinateRing C)), hrel⟩
  have hclosure : closure ({eta} : Set (ProjectiveSpectrum (grading C))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply (ProjectiveSpectrum.le_iff_mem_closure (grading C) eta x).mp
    change (⊥ : HomogeneousIdeal (grading C)) ≤ x.asHomogeneousIdeal
    exact bot_le
  letI : IrreducibleSpace X := by
    apply (irreducibleSpace_def X).mpr
    change IsIrreducible (Set.univ : Set (ProjectiveSpectrum (grading C)))
    rw [← hclosure]
    exact isIrreducible_singleton.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- Starting only with the original homogeneous quotient and OWN closed point,
the actual minimal component is constructed and its native integrality is
proved. Its same original-K residue point/degree is retained. -/
theorem homogeneousProjective_originalClosedPoint_exists_integralMinimalComponent
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : closedPoints (scheme I)) :
    ∃ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hIC : I.toIdeal ≤ C.toIdeal),
      C.toIdeal ∈ I.toIdeal.minimalPrimes ∧ C.toIdeal.IsPrime ∧
      IsIntegral (scheme C) ∧
      ∃ Q : closedPoints (scheme C),
        schemeQuotientMap I C hIC Q.1 = P.1 ∧
        IsIso ((schemeQuotientMap I C hIC).residueFieldMap Q.1) ∧
        (toBase C).residueDegree Q.1 = (toBase I).residueDegree P.1 := by
  obtain ⟨C, hIC, hCmin, hCprime, Q, hpoint, hresidue, hdegree⟩ :=
    homogeneousProjective_originalClosedPoint_exists_minimalComponent I P
  exact ⟨C, hIC, hCmin, hCprime,
    homogeneousPrime_projectiveScheme_isIntegral C hCprime Q.1,
    Q, hpoint, hresidue, hdegree⟩

/-- Every actual component/subscheme chart is a literal surjective quotient
of the selected p/q chart, so dimension <=1 descends. No integrality or minimal
prime premise is needed for this chart bound. -/
theorem selectedProjectiveComponent_chart_ringKrullDim_le_one
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (j : Fin 4) :
    ringKrullDim (ChartRing C j) ≤ 1 := by
  exact (ringKrullDim_le_of_surjective
    (chartQuotientMap (projectiveIntersectionIdeal p q hp hq) C hIC j)
    (chartQuotientMap_surjective (projectiveIntersectionIdeal p q hp hq) C hIC j)).trans
      (projectiveIntersection_chart_ringKrullDim_le_one p q hp hp0 n hq hnot j)

/-- The OWN native component stalk has dimension <=1 by its actual coordinate
chart and actual affine prime localization. This consumes only the actual
subscheme equations, smooth cubic and selected q nonmembership. -/
theorem selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (P : scheme C) :
    ringKrullDim ((scheme C).presheaf.stalk P) ≤ 1 := by
  let X := scheme C
  obtain ⟨j, z, hz⟩ := exists_coordinate_chart C P
  let U := (chartι C j).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (chartι C j)
  have hPU : P ∈ U := ⟨z, hz⟩
  let e : Γ(X, U) ≃+* ChartRing C j :=
    ((IsOpenImmersion.ΓIsoTop (chartι C j)).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (ChartRing C j))).commRingCatIsoToRingEquiv
  have hdim : ringKrullDim Γ(X, U) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact selectedProjectiveComponent_chart_ringKrullDim_le_one p q hp hp0 n hq hnot C hIC j
  let J := (hU.primeIdealOf ⟨P, hPU⟩).asIdeal
  letI : J.IsPrime := (hU.primeIdealOf ⟨P, hPU⟩).isPrime
  letI : Algebra Γ(X, U) (X.presheaf.stalk P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk P) J := hU.isLocalization_stalk ⟨P, hPU⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height J (X.presheaf.stalk P)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := J))).trans hdim

/-- Actual original selected p/q curve point produces an integral minimal
component with all OWN native stalk dimensions <=1 and the SAME original-K
closed point and residue degree. The whole p/q curve may be nonintegral. -/
theorem selectedProjectiveCurve_originalClosedPoint_exists_integralCurveComponent
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq))) :
    ∃ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal),
      C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes ∧
      C.toIdeal.IsPrime ∧ IsIntegral (scheme C) ∧
      (∀ x : scheme C, ringKrullDim ((scheme C).presheaf.stalk x) ≤ 1) ∧
      ∃ Q : closedPoints (scheme C),
        schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) C hIC Q.1 = P.1 ∧
        IsIso ((schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) C hIC).residueFieldMap Q.1) ∧
        (toBase C).residueDegree Q.1 =
          (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 := by
  obtain ⟨C, hIC, hmin, hprime, hint, Q, hpoint, hresidue, hdegree⟩ :=
    homogeneousProjective_originalClosedPoint_exists_integralMinimalComponent
      (projectiveIntersectionIdeal p q hp hq) P
  exact ⟨C, hIC, hmin, hprime, hint,
    selectedProjectiveComponent_original_stalk_ringKrullDim_le_one p q hp hp0 n hq hnot C hIC,
    Q, hpoint, hresidue, hdegree⟩

end PfaffianDescent.Coray
