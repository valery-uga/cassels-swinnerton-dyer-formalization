import PfaffianDescent.VoisinCubicSurfaceChartRegular
import PfaffianDescent.VoisinPlaneConicAtPrimeCartier

/-!
# Domain property of every standard chart of a smooth cubic

A smooth nonzero cubic is irreducible, hence its homogeneous coordinate
ring is a domain. Each standard coordinate survives in this quotient,
so localization at its powers is again a domain. The actual degree-zero
homogeneous chart ring embeds in that localization.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every standard affine chart ring of a smooth nonzero cubic hypersurface
is a domain, including charts containing no ground-field rational point. -/
theorem smoothCubic_chartRing_isDomain
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) : IsDomain (ChartRing (equationIdeal p hp) j) := by
  let I := equationIdeal p hp
  have hprime : I.toIdeal.IsPrime := by
    change (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime
    exact principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing I) :=
    (Ideal.Quotient.isDomain_iff_prime I.toIdeal).mpr hprime
  have hz : coordinate I j ≠ 0 := by
    intro hzero
    have hmem : X j ∈ I.toIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp hzero
    exact coordinate_not_mem_cubic_ideal p hp hp0 j hmem
  let M := Submonoid.powers (coordinate I j)
  have hM : M ≤ nonZeroDivisors (CoordinateRing I) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hz)
  letI : IsDomain (Localization M) :=
    IsLocalization.isDomain_localization hM
  exact (HomogeneousLocalization.val_injective M).isDomain
    (algebraMap (ChartRing I j) (Localization M))

/-- A nonzero homogeneous polynomial of degree below three remains nonzero
on every standard affine chart of a smooth cubic. In particular, the linear
equation of a genuine plane cannot become the zero equation on a chart. -/
theorem smoothCubic_chartEval_ne_zero_of_degree_lt_three
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (f : MvPolynomial (Fin 4) K) (d : ℕ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : d < 3)
    (j : Fin 4) :
    f.eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j) ≠ 0 := by
  let I := equationIdeal p hp
  have hprime : I.toIdeal.IsPrime := by
    change (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime
    exact principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing I) :=
    (Ideal.Quotient.isDomain_iff_prime I.toIdeal).mpr hprime
  have hz : coordinate I j ≠ 0 := by
    intro hzero
    have hmem : X j ∈ I.toIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp hzero
    exact coordinate_not_mem_cubic_ideal p hp hp0 j hmem
  let M := Submonoid.powers (coordinate I j)
  have hM : M ≤ nonZeroDivisors (CoordinateRing I) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hz)
  intro hzero
  have hfrac0 : Away.mk (grading I) (coordinate_mem I j) d
      (Ideal.Quotient.mk I.toIdeal f)
      (by simpa using polynomial_class_mem_grading I f hf) = 0 := by
    rw [← eval₂_chartCoordinate_eq_fraction I j f hf]
    exact hzero
  have hval := congrArg HomogeneousLocalization.val hfrac0
  simp only [Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'] at hval
  obtain ⟨m, hm⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hval
  have hmne : (m : CoordinateRing I) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (hM m.property)
  have hq0 : Ideal.Quotient.mk I.toIdeal f = 0 :=
    (mul_eq_zero.mp hm).resolve_left hmne
  have hdiv : p ∣ f :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hq0)
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hf0
  rw [hp.totalDegree hp0, hf.totalDegree hf0] at hle
  omega

/-- On a smooth cubic chart, the Jacobian criterion and a nonzero conic
ideal give a regular local equation for the plane conic at every point.
The domain hypothesis in the algebraic local Cartier lemma follows from
smoothness and need not be supplied separately. -/
theorem smoothCubic_planeConic_atPrime_regularPrincipal_of_jacobian_top
    (p ell q a b : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (h : p = ell * a + q * b)
    (j : Fin 4)
    (hnonzero :
      let I := equationIdeal p hp
      ell.eval₂ (chartBaseMap I j) (chartCoordinate I j) ≠ 0 ∨
        q.eval₂ (chartBaseMap I j) (chartCoordinate I j) ≠ 0)
    (hjac :
      let I := equationIdeal p hp
      Ideal.span (Set.range (fun i : Fin 4 =>
        (pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤)
    (P : PrimeSpectrum (ChartRing (equationIdeal p hp) j)) :
    let I := equationIdeal p hp
    let f : ChartRing I j →+* Localization.AtPrime P.asIdeal := algebraMap _ _
    ∃ z : Localization.AtPrime P.asIdeal, IsRegular z ∧
      Ideal.span
          ({f (ell.eval₂ (chartBaseMap I j) (chartCoordinate I j)),
            f (q.eval₂ (chartBaseMap I j) (chartCoordinate I j))} :
            Set (Localization.AtPrime P.asIdeal)) =
        Ideal.span ({z} : Set (Localization.AtPrime P.asIdeal)) := by
  letI : IsDomain (ChartRing (equationIdeal p hp) j) :=
    smoothCubic_chartRing_isDomain p hp hp0 j
  exact planeConic_cubicChart_atPrime_regularPrincipal_of_jacobian_top
    p ell q a b hp h j hnonzero hjac P

/-- If the plane equation is a nonzero homogeneous linear form, the
nonzero-ideal premise of the local Cartier certificate follows on every
standard chart of the smooth cubic. -/
theorem smoothCubic_planeConic_atPrime_regularPrincipal_of_jacobian_top_of_linear
    (p ell q a b : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (h : p = ell * a + q * b)
    (j : Fin 4)
    (hjac :
      let I := equationIdeal p hp
      Ideal.span (Set.range (fun i : Fin 4 =>
        (pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤)
    (P : PrimeSpectrum (ChartRing (equationIdeal p hp) j)) :
    let I := equationIdeal p hp
    let f : ChartRing I j →+* Localization.AtPrime P.asIdeal := algebraMap _ _
    ∃ z : Localization.AtPrime P.asIdeal, IsRegular z ∧
      Ideal.span
          ({f (ell.eval₂ (chartBaseMap I j) (chartCoordinate I j)),
            f (q.eval₂ (chartBaseMap I j) (chartCoordinate I j))} :
            Set (Localization.AtPrime P.asIdeal)) =
        Ideal.span ({z} : Set (Localization.AtPrime P.asIdeal)) := by
  apply smoothCubic_planeConic_atPrime_regularPrincipal_of_jacobian_top
    p ell q a b hp hp0 h j (Or.inl ?_) hjac P
  exact smoothCubic_chartEval_ne_zero_of_degree_lt_three
    p hp hp0 ell 1 hell hell0 (by omega) j

end PfaffianDescent
