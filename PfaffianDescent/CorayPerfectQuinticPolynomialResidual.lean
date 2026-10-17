import PfaffianDescent.CorayPerfectQuinticCoordinates
import PfaffianDescent.QuarticTwistedCubicResidual
import PfaffianDescent.CorayEffectiveCyclePointBound
import AllCharacteristics.ProjectivePoints
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! SOURCE ONLY / UNVERIFIED. Perfect-field noncoplanar degree-five
residual construction, using the literal homogeneous polynomial and
original ground-field matrix. No Euler cubic tensor, desired residual
factor, geometric-integrality, genus, or smaller-point premise is used.
-/
noncomputable section
namespace PfaffianDescent.Coray
open Polynomial Module AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogeneous evaluation scales by the degree in every characteristic.
This is proved from the actual coefficient expansion. -/
theorem homogeneous_eval₂_scaledCoordinates
    {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Fintype σ]
    (c : R →+* S) (f : MvPolynomial σ R) (n : ℕ)
    (hf : f.IsHomogeneous n) (v : S) (x : σ → S) :
    MvPolynomial.eval₂ c (fun i => v * x i) f =
      v ^ n * MvPolynomial.eval₂ c x f := by
  classical
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdegree : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.mp hd)
  have hsum : (∑ i, d i) = n := (Finsupp.degree_eq_sum d).symm.trans hdegree
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  ring

private def twistedRestrictionPolynomial
    {K : Type u} [Field K] (f : MvPolynomial (Fin 4) K) : K[X] :=
  QuarticNet.binaryDehomogenize (QuarticNet.standardTwistedCubicParam K f)

private theorem twistedRestriction_homogeneous
    {K : Type u} [Field K] (f : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) :
    (QuarticNet.standardTwistedCubicParam K f).IsHomogeneous 9 := by
  simpa only [Nat.reduceMul] using QuarticNet.standardTwistedCubicParam_homogeneous hf

private theorem twistedRestriction_eval
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (f : MvPolynomial (Fin 4) K) (a : A) :
    Polynomial.aeval a (twistedRestrictionPolynomial f) =
      MvPolynomial.aeval (fun i : Fin 4 => a ^ (i : ℕ)) f := by
  have hparam : QuarticNet.cubicVeronese (1 : A) a =
      (fun i : Fin 4 => a ^ (i : ℕ)) := by
    funext i
    fin_cases i <;> simp [QuarticNet.cubicVeronese]
  rw [twistedRestrictionPolynomial, QuarticNet.binaryDehomogenize_eval,
    QuarticNet.standardTwistedCubicParam_eval, hparam]

private theorem twistedRestriction_topCoeff
    {K : Type u} [Field K] (f : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) :
    (twistedRestrictionPolynomial f).coeff 9 =
      MvPolynomial.aeval (Pi.single 3 1 : Vec K 4) f := by
  have hparam : QuarticNet.cubicVeronese (0 : K) 1 =
      (Pi.single 3 1 : Vec K 4) := by
    funext i
    fin_cases i <;> simp [QuarticNet.cubicVeronese, Pi.single_apply]
  rw [twistedRestrictionPolynomial,
    QuarticNet.binaryDehomogenize_topCoeff 9 _ (twistedRestriction_homogeneous f hf),
    QuarticNet.standardTwistedCubicParam_eval, hparam]

private theorem homogeneous_quintic_actual_residual
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (a : L) (ha : (minpoly K a).natDegree = 5)
    (he : MvPolynomial.aeval (fun i : Fin 4 => a ^ (i : ℕ)) f = 0) :
    MvPolynomial.aeval (Pi.single 3 1 : Vec K 4) f = 0 ∨
      ∃ q : K[X], q.natDegree = 4 ∧
        twistedRestrictionPolynomial f = minpoly K a * q := by
  by_cases hlast : MvPolynomial.aeval (Pi.single 3 1 : Vec K 4) f = 0
  · exact Or.inl hlast
  right
  have hcoeff : (twistedRestrictionPolynomial f).coeff 9 ≠ 0 := by
    rw [twistedRestriction_topCoeff f hf]
    exact hlast
  have hdeg : (twistedRestrictionPolynomial f).natDegree = 9 :=
    le_antisymm
      (QuarticNet.binaryDehomogenize_natDegree 9 _ (twistedRestriction_homogeneous f hf))
      (le_natDegree_of_ne_zero hcoeff)
  have hpoly0 : twistedRestrictionPolynomial f ≠ 0 := by
    intro hz
    apply hcoeff
    rw [hz]
    exact coeff_zero _
  have heval : Polynomial.aeval a (twistedRestrictionPolynomial f) = 0 := by
    rw [twistedRestriction_eval]
    exact he
  obtain ⟨q, hq⟩ := minpoly.dvd K a heval
  have hmin0 : minpoly K a ≠ 0 := by
    intro hz
    simp [hz] at ha
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hq
    exact hpoly0 hq
  have hdegrees : 9 = 5 + q.natDegree := by
    rw [← hdeg, hq, natDegree_mul hmin0 hq0, ha]
  exact ⟨q, by omega, hq⟩

private theorem quartic_irreducible_factor_small
    {K : Type u} [Field K] (q : K[X]) (hq : q.natDegree = 4) :
    ∃ r : K[X], Irreducible r ∧ r ∣ q ∧
      (r.natDegree = 1 ∨ r.natDegree = 2 ∨ r.natDegree = 4) := by
  have hq0 : q ≠ 0 := by intro hz; simp [hz] at hq
  by_cases hi : Irreducible q
  · exact ⟨q, hi, dvd_refl q, Or.inr (Or.inr hq)⟩
  have hu : ¬ IsUnit q := not_isUnit_of_natDegree_pos q (by omega)
  rw [irreducible_iff_lt_natDegree_lt hq0 hu] at hi
  push Not at hi
  obtain ⟨p, hp, hd, hpdvd⟩ := hi
  have hpdeg : 0 < p.natDegree ∧ p.natDegree ≤ 2 := by
    simpa only [hq, Nat.reduceDiv, Finset.mem_Ioc] using hd
  obtain ⟨r, hr, hrdvd⟩ := exists_irreducible_of_natDegree_pos hpdeg.1
  have hrpos : 0 < r.natDegree := hr.natDegree_pos
  have hrle : r.natDegree ≤ 2 :=
    (natDegree_le_of_dvd hrdvd hp.ne_zero).trans hpdeg.2
  refine ⟨r, hr, hrdvd.trans hpdvd, ?_⟩
  omega

private theorem coefficient_matrix_mulVec_injective
    {K F : Type u} [Field K] [Field F] (f : K →+* F)
    (M : Mat K 4) (hM : Function.Injective M.mulVec) :
    Function.Injective (M.map f).mulVec := by
  have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
  have hmapdet : IsUnit (M.map f).det := by
    change IsUnit (f.mapMatrix M).det
    rw [← f.map_det M]
    exact hdet.map f
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det (M.map f)).mpr hmapdet)

private theorem original_cycle_from_polynomial_transformed_coordinates
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (M : Mat K 4) (hM : Function.Injective M.mulVec)
    (v : Vec F 4) (hv : v ≠ 0)
    (he : MvPolynomial.aeval v (linearSubstitution M f) = 0) :
    ∃ z : EffectiveZeroCycle (hypersurface f hf),
      EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = finrank K F := by
  let y : Vec F 4 := (M.map (algebraMap K F)).mulVec v
  have hy : y ≠ 0 := by
    intro hz
    apply hv
    apply coefficient_matrix_mulVec_injective (algebraMap K F) M hM
    simpa only [Matrix.mulVec_zero] using hz
  have hfy : MvPolynomial.eval₂ (algebraMap K F) y f = 0 := by
    rw [linearSubstitution_aeval, MvPolynomial.aeval_def] at he
    exact he
  obtain ⟨q, hq⟩ := hypersurface_point_of_coordinates (algebraMap K F) f hf y hy hfy
  exact exists_effectiveZeroCycle_of_finite_algebra_point
    (hypersurfaceToBase f hf) q hq

/-- A noncoplanar quintic point over the ORIGINAL perfect K constructs
an actual cycle of degree one, two, or four on the ORIGINAL cubic.
The degree-nine restriction, minpoly quotient, and factor field are
all constructed internally; the original matrix and scalar are retained. -/
theorem perfectField_originalNoncoplanarQuintic_exists_actual_smallDegree_cycle
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 5)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (p : Vec L 4) (hp : LinearIndependent K p)
    (hF : MvPolynomial.eval₂ (algebraMap K L) p f = 0) :
    ∃ z : EffectiveZeroCycle (hypersurface f hf),
      EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 1 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 2 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 4 := by
  obtain ⟨a, ha, v, hv, M, hM, hcoord⟩ :=
    perfectField_independentQuinticCoordinates hdim p hp
  have hscaled : v ^ 3 * MvPolynomial.eval₂ (algebraMap K L)
      ((M.map (algebraMap K L)).mulVec (fun i : Fin 4 => a ^ (i : ℕ))) f = 0 := by
    rw [← homogeneous_eval₂_scaledCoordinates (algebraMap K L) f 3 hf]
    rw [hcoord] at hF
    have hscale : (v • (M.map (algebraMap K L)).mulVec
        (fun i : Fin 4 => a ^ (i : ℕ)) : Vec L 4) =
        (fun i => v * (M.map (algebraMap K L)).mulVec
          (fun j : Fin 4 => a ^ (j : ℕ)) i) := by
      funext i
      rfl
    rw [hscale] at hF
    exact hF
  have hcanon : MvPolynomial.aeval (fun i : Fin 4 => a ^ (i : ℕ))
      (linearSubstitution M f) = 0 := by
    rw [linearSubstitution_aeval, MvPolynomial.aeval_def]
    exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 3 hv)
  have htrans : (linearSubstitution M f).IsHomogeneous 3 :=
    linearSubstitution_homogeneous M hf
  rcases homogeneous_quintic_actual_residual (linearSubstitution M f) htrans a ha hcanon
      with hlast | hres
  · have hvertex : (Pi.single 3 1 : Vec K 4) ≠ 0 := by
      intro hz
      have hzero : (1 : K) = 0 := by
        have h := congrFun hz (3 : Fin 4)
        simpa only [Pi.single_eq_same, Pi.zero_apply] using h
      exact (one_ne_zero : (1 : K) ≠ 0) hzero
    obtain ⟨z, hz⟩ := original_cycle_from_polynomial_transformed_coordinates
      f hf M hM (Pi.single 3 1) hvertex hlast
    exact ⟨z, Or.inl (by simpa using hz)⟩
  · obtain ⟨q, hqdeg, hquot⟩ := hres
    obtain ⟨r, hr, hrdvd, hrdeg⟩ := quartic_irreducible_factor_small q hqdeg
    letI : Fact (Irreducible r) := ⟨hr⟩
    let F := AdjoinRoot r
    letI : FiniteDimensional K F :=
      Module.Finite.of_basis (AdjoinRoot.powerBasis hr.ne_zero).basis
    have hdimF : finrank K F = r.natDegree := by
      rw [(AdjoinRoot.powerBasis hr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    let w : Vec F 4 := fun i => (AdjoinRoot.root r) ^ (i : ℕ)
    have hw : w ≠ 0 := by
      intro hz
      have hzero : (1 : F) = 0 := by
        have h := congrFun hz (0 : Fin 4)
        simpa only [w, Fin.val_zero, pow_zero, Pi.zero_apply] using h
      exact (one_ne_zero : (1 : F) ≠ 0) hzero
    have hrwhole : r ∣ twistedRestrictionPolynomial (linearSubstitution M f) := by
      rw [hquot]
      exact dvd_mul_of_dvd_right hrdvd _
    have he : eval₂ (algebraMap K F) (AdjoinRoot.root r)
        (twistedRestrictionPolynomial (linearSubstitution M f)) = 0 := by
      obtain ⟨s, hs⟩ := hrwhole
      rw [hs, eval₂_mul]
      have hroot : eval₂ (algebraMap K F) (AdjoinRoot.root r) r = 0 := by
        change eval₂ (algebraMap K (AdjoinRoot r)) (AdjoinRoot.root r) r = 0
        rw [AdjoinRoot.algebraMap_eq]
        exact AdjoinRoot.eval₂_root r
      rw [hroot, zero_mul]
    have hwvalue : MvPolynomial.aeval w (linearSubstitution M f) = 0 := by
      change MvPolynomial.aeval
        (fun i : Fin 4 => (AdjoinRoot.root r) ^ (i : ℕ)) (linearSubstitution M f) = 0
      rw [← twistedRestriction_eval, Polynomial.aeval_def]
      exact he
    obtain ⟨z, hz⟩ := original_cycle_from_polynomial_transformed_coordinates
      f hf M hM w hw hwvalue
    refine ⟨z, ?_⟩
    rw [hz, hdimF]
    exact hrdeg

/-- The internally constructed cycle supplies a smaller ORIGINAL-K closed
point, retaining its full residue degree through the actual pushforward. -/
theorem perfectField_originalNoncoplanarQuintic_exists_smaller_originalCubic_closedPoint
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 5)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (p : Vec L 4) (hp : LinearIndependent K p)
    (hF : MvPolynomial.eval₂ (algebraMap K L) p f = 0) :
    ∃ R : closedPoints (hypersurface f hf),
      Nat.Coprime ((hypersurfaceToBase f hf).residueDegree R.1) 3 ∧
      (hypersurfaceToBase f hf).residueDegree R.1 ≤ 4 ∧
      (hypersurfaceToBase f hf).residueDegree R.1 < 5 := by
  obtain ⟨z, hz⟩ := perfectField_originalNoncoplanarQuintic_exists_actual_smallDegree_cycle
    hdim f hf p hp hF
  have hcop : Nat.Coprime (EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z) 3 := by
    rcases hz with h | h | h <;> rw [h] <;> decide
  have hbound : EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z ≤ 4 := by
    rcases hz with h | h | h <;> omega
  obtain ⟨R, _, hRcop, hRle⟩ :=
    effectiveCycle_coprime_degree_has_bounded_closedPoint (hypersurfaceToBase f hf) z hcop
  exact ⟨R, hRcop, hRle.trans hbound, by omega⟩

end PfaffianDescent.Coray
