import PfaffianDescent.IndependentQuinticPoint
import PfaffianDescent.TwistedCubic
import PfaffianDescent.MultivariateCubic
import PfaffianDescent.CorayEffectiveCyclePointBound
import AllCharacteristics.ProjectivePoints
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! SOURCE ONLY / UNVERIFIED. Coray Proposition 3.1, r=1, with the
arithmetic residual calculation authorized explicitly in footnote 13.
The original ground-field matrix and common scalar are constructed from
the actual noncoplanar quintic coordinates. No genus, geometric integrality,
rank-two image, residual factor, or smaller-point conclusion is supplied.
-/

noncomputable section
namespace PfaffianDescent.Coray
open Polynomial Module AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

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

private theorem canonical_quintic_actual_residual
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (c : Cubic K 4) (a : L) (ha : (minpoly K a).natDegree = 5)
    (he : (c.map (algebraMap K L)).eval (fun i => a ^ (i : ℕ)) = 0) :
    c.eval (Pi.single 3 1) = 0 ∨
      ∃ q : K[X], q.natDegree = 4 ∧
        c.twistedPolynomial = minpoly K a * q := by
  by_cases hlast : c (3, 3, 3) = 0
  · exact Or.inl ((Cubic.eval_last_coordinate c).trans hlast)
  right
  have hcoeff : c.twistedPolynomial.coeff 9 ≠ 0 := by
    rw [Cubic.twistedPolynomial_coeff_nine]
    exact hlast
  have hdeg : c.twistedPolynomial.natDegree = 9 :=
    le_antisymm (Cubic.twistedPolynomial_degree_le c)
      (le_natDegree_of_ne_zero hcoeff)
  have hpoly0 : c.twistedPolynomial ≠ 0 := by
    intro hz
    apply hcoeff
    rw [hz]
    exact coeff_zero _
  have heval : aeval a c.twistedPolynomial = 0 := by
    rw [aeval_def, Cubic.twistedPolynomial_eval₂]
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

private theorem original_cycle_from_transformed_coordinates
    {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]
    [FiniteDimensional K F]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = f)
    (M : Mat K 4) (hM : Function.Injective M.mulVec)
    (v : Vec F 4) (hv : v ≠ 0)
    (he : ((c.compLinear M).map (algebraMap K F)).eval v = 0) :
    ∃ z : EffectiveZeroCycle (hypersurface f hf),
      EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = finrank K F := by
  let y : Vec F 4 := (M.map (algebraMap K F)).mulVec v
  have hy : y ≠ 0 := by
    intro hz
    apply hv
    apply coefficient_matrix_mulVec_injective (algebraMap K F) M hM
    simpa only [Matrix.mulVec_zero] using hz
  have hcy : (c.map (algebraMap K F)).eval y = 0 := by
    rw [Cubic.compLinear_map, Cubic.eval_compLinear] at he
    exact he
  have hfy : MvPolynomial.eval₂ (algebraMap K F) y f = 0 := by
    rw [← hc, Cubic.eval_toMvPolynomial]
    exact hcy
  obtain ⟨q, hq⟩ := hypersurface_point_of_coordinates (algebraMap K F) f hf y hy hfy
  exact exists_effectiveZeroCycle_of_finite_algebra_point
    (hypersurfaceToBase f hf) q hq

/-- Actual noncoplanar quintic coordinates on the ORIGINAL cubic construct
an effective cycle of degree one, two, or four. The residual polynomial
and its irreducible factor are constructed inside the proof. -/
theorem originalNoncoplanarQuintic_exists_actual_smallDegree_cycle
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 5)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (p : Vec L 4) (hp : LinearIndependent K p)
    (hF : MvPolynomial.eval₂ (algebraMap K L) p f = 0) :
    ∃ z : EffectiveZeroCycle (hypersurface f hf),
      EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 1 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 2 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 4 := by
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor f hf
  have hcp : (c.map (algebraMap K L)).eval p = 0 := by
    rw [← Cubic.eval_toMvPolynomial, hc]
    exact hF
  obtain ⟨a, b, hb, v, hv, M, hM, hcoord⟩ :=
    independent_quintic_coordinates hdim p hp
  let pb : PowerBasis K L :=
    { gen := a, dim := 5, basis := b, basis_eq_pow := hb }
  have ha : (minpoly K a).natDegree = 5 := pb.natDegree_minpoly
  rw [hcoord, Cubic.eval_smul] at hcp
  have hnonzero : v ^ 3 ≠ 0 := pow_ne_zero 3 hv
  have hcanon : ((c.compLinear M).map (algebraMap K L)).eval
      (fun i => a ^ (i : ℕ)) = 0 := by
    rw [Cubic.compLinear_map, Cubic.eval_compLinear]
    have hpowers : rationalCubicCoordinates a = (fun i : Fin 4 => a ^ (i : ℕ)) := by
      funext i
      fin_cases i <;> simp [rationalCubicCoordinates]
    rw [hpowers] at hcp
    exact (mul_eq_zero.mp hcp).resolve_left hnonzero
  rcases canonical_quintic_actual_residual (c.compLinear M) a ha hcanon with hlast | hres
  · have hvertex : (Pi.single 3 1 : Vec K 4) ≠ 0 := by
      intro hz
      have hzero : (1 : K) = 0 := by
        have h := congrFun hz (3 : Fin 4)
        simpa only [Pi.single_eq_same, Pi.zero_apply] using h
      exact (one_ne_zero : (1 : K) ≠ 0) hzero
    have he : ((c.compLinear M).map (algebraMap K K)).eval
        (Pi.single 3 1) = 0 := by
      have hid : (c.compLinear M).map (algebraMap K K) = c.compLinear M := by
        funext i
        change algebraMap K K (c.compLinear M i) = c.compLinear M i
        simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [hid]
      exact hlast
    obtain ⟨z, hz⟩ := original_cycle_from_transformed_coordinates
      f hf c hc M hM (Pi.single 3 1) hvertex he
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
    have hrwhole : r ∣ (c.compLinear M).twistedPolynomial := by
      rw [hquot]
      exact dvd_mul_of_dvd_right hrdvd _
    have he : eval₂ (algebraMap K F) (AdjoinRoot.root r)
        (c.compLinear M).twistedPolynomial = 0 := by
      obtain ⟨s, hs⟩ := hrwhole
      rw [hs, eval₂_mul]
      have hroot : eval₂ (algebraMap K F) (AdjoinRoot.root r) r = 0 := by
        change eval₂ (algebraMap K (AdjoinRoot r)) (AdjoinRoot.root r) r = 0
        rw [AdjoinRoot.algebraMap_eq]
        exact AdjoinRoot.eval₂_root r
      rw [hroot, zero_mul]
    have hcw : ((c.compLinear M).map (algebraMap K F)).eval w = 0 := by
      rw [Cubic.twistedPolynomial_eval₂] at he
      exact he
    obtain ⟨z, hz⟩ := original_cycle_from_transformed_coordinates
      f hf c hc M hM w hw hcw
    refine ⟨z, ?_⟩
    rw [hz, hdimF]
    exact hrdeg

/-- The actual cycle supplies a smaller point on the ORIGINAL cubic over
the ORIGINAL K. Full residue degrees are retained through the proper
pushforward from the internally constructed factor field. -/
theorem originalNoncoplanarQuintic_exists_smaller_originalCubic_closedPoint
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 5)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (p : Vec L 4) (hp : LinearIndependent K p)
    (hF : MvPolynomial.eval₂ (algebraMap K L) p f = 0) :
    ∃ R : closedPoints (hypersurface f hf),
      Nat.Coprime ((hypersurfaceToBase f hf).residueDegree R.1) 3 ∧
      (hypersurfaceToBase f hf).residueDegree R.1 ≤ 4 ∧
      (hypersurfaceToBase f hf).residueDegree R.1 < 5 := by
  obtain ⟨z, hz⟩ := originalNoncoplanarQuintic_exists_actual_smallDegree_cycle
    hdim f hf p hp hF
  have hcop : Nat.Coprime (EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z) 3 := by
    rcases hz with h | h | h <;> rw [h] <;> decide
  have hbound : EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z ≤ 4 := by
    rcases hz with h | h | h <;> omega
  obtain ⟨R, _, hRcop, hRle⟩ :=
    effectiveCycle_coprime_degree_has_bounded_closedPoint (hypersurfaceToBase f hf) z hcop
  exact ⟨R, hRcop, hRle.trans hbound, by omega⟩

end PfaffianDescent.Coray
