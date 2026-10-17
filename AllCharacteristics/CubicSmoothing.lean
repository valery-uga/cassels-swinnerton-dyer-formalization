import AllCharacteristics.CubicPencilSmooth
import AllCharacteristics.ExternalDegreeReduction
import AllCharacteristics.CoprimeEffectiveCycle
import AllCharacteristics.SchemeSpecialization
import AllCharacteristics.SmoothLocusFinitePointLifting
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Smoothing a cubic surface from one smooth finite-extension point

This is the valuative core of the paper's removal of the smoothness
hypothesis.  The only external input isolated here is the smooth-point case of
Ma's degree-preserving lifting theorem.  The pencil, its generic smoothness,
the prime-to-three cycle calculation, the smooth cubic theorem, and proper
specialization are all the actual constructions proved in this development.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective

universe u

/-- Coordinate form of a smooth projective point: the vector is nonzero, lies
on the equation, and at least one partial derivative is nonzero. -/
def IsSmoothCubicCoordinatePoint {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (x : Fin 4 → K) : Prop :=
  x ≠ 0 ∧ p.eval x = 0 ∧
    ∃ i : Fin 4, (MvPolynomial.pderiv i p).eval x ≠ 0

/-- The generic equation of the power-series pencil used in the smoothing
argument. -/
noncomputable def powerSeriesPencilGeneric {k : Type u} [Field k]
    (p q : MvPolynomial (Fin 4) k) :
    MvPolynomial (Fin 4) (FractionRing (PowerSeries k)) :=
  (cubicPencil p q).map
    ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp
      Polynomial.coeToPowerSeries.ringHom)

/-- Its inherited degree-three homogeneity. -/
theorem powerSeriesPencilGeneric_isHomogeneous {k : Type u} [Field k]
    {p q : MvPolynomial (Fin 4) k}
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) :
    (powerSeriesPencilGeneric p q).IsHomogeneous 3 :=
  (cubicPencil_isHomogeneous hp hq).map _

/-- The precise special case of Ma's smooth-point lifting result used by the
paper.  It retains the full degree even for inseparable residue extensions.
The result is passed explicitly, rather than installed as an axiom. -/
def MaCubicPencilPointLiftingFor (k : Type u) [Field k] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra k L] [Module.Finite k L]
    (p q : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → L),
    IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) x →
    ∃ z : EffectiveZeroCycle
        (hypersurface (powerSeriesPencilGeneric p q)
          (powerSeriesPencilGeneric_isHomogeneous hp hq)),
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (powerSeriesPencilGeneric p q)
          (powerSeriesPencilGeneric_isHomogeneous hp hq)) z =
        Module.finrank k L

/-- The smooth-cubic hypothesis of `prop:smoothing`, stated as rational
sections rather than coordinate vectors. -/
def SmoothCubicZeroCyclePointFor (K : Type u) [Field K] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
    ∀ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1 →
      ∃ s : Spec (.of K) ⟶ hypersurface p hp,
        s ≫ hypersurfaceToBase p hp = 𝟙 _

/-- A smooth point over a finite extension of degree prime to three can be
lifted through a smooth cubic pencil and then descended back to a point of the
original, possibly singular, cubic by the smooth theorem and properness. -/
theorem cubic_coordinates_of_smooth_extension_point_of_voisin_ma
    (voisin : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeOneOrFourFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (ma : MaCubicPencilPointLiftingFor k)
    (p q : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    (hqs : Smooth (hypersurfaceToBase q hq))
    (x : Fin 4 → L)
    (hx : IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) x)
    (hdegree : Nat.Coprime (Module.finrank k L) 3) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  let R := PowerSeries k
  let K := FractionRing R
  let a : Polynomial k →+* R := Polynomial.coeToPowerSeries.ringHom
  let g : Polynomial k →+* K := (algebraMap R K).comp a
  have hg : Function.Injective g :=
    (FaithfulSMul.algebraMap_injective R K).comp (Polynomial.coe_injective k)
  let _ : Smooth (hypersurfaceToBase q hq) := hqs
  have hgenericSmooth : Smooth
      (hypersurfaceToBase (powerSeriesPencilGeneric p q)
        (powerSeriesPencilGeneric_isHomogeneous hp hq)) := by
    exact cubicPencil_map_smooth g hg hp hq hq0
  let _ : Smooth
      (hypersurfaceToBase (powerSeriesPencilGeneric p q)
        (powerSeriesPencilGeneric_isHomogeneous hp hq)) := hgenericSmooth

  obtain ⟨z, hz⟩ := ma L p q hp hq x hx
  have hzcoprime : Nat.Coprime
      (EffectiveZeroCycle.degree
        (hypersurfaceToBase (powerSeriesPencilGeneric p q)
          (powerSeriesPencilGeneric_isHomogeneous hp hq)) z) 3 := by
    rw [hz]
    exact hdegree
  obtain ⟨w, hw⟩ := cubicSurface_zeroCycle_degree_one_of_effective_coprime
    (powerSeriesPencilGeneric p q)
    (powerSeriesPencilGeneric_isHomogeneous hp hq) z hzcoprime
  have hgeneric0 : powerSeriesPencilGeneric p q ≠ 0 := by
    change (cubicPencil p q).map g ≠ 0
    intro h
    apply cubicPencil_ne_zero_of_right hq0
    apply MvPolynomial.map_injective g hg
    simpa only [map_zero] using h
  obtain ⟨y, hy, hey⟩ :=
    smooth_cubic_coordinates_of_zeroCycle_degree_one_of_voisin voisin
      (powerSeriesPencilGeneric p q)
      (powerSeriesPencilGeneric_isHomogeneous hp hq)
      hgeneric0 w hw

  let P : MvPolynomial (Fin 4) R := (cubicPencil p q).map a
  have hP : P.IsHomogeneous 3 := (cubicPencil_isHomogeneous hp hq).map a
  have hPK : P.map (algebraMap R K) = powerSeriesPencilGeneric p q := by
    change ((cubicPencil p q).map a).map (algebraMap R K) = _
    rw [powerSeriesPencilGeneric, MvPolynomial.map_map]
  obtain ⟨yK, hyK⟩ := hypersurface_point_of_coordinates
    (algebraMap R K) P hP y hy (by
      rw [← MvPolynomial.eval_map, hPK]
      exact hey)
  let f := hypersurfaceToBase P hP
  have hpointK : HasPointOver f (algebraMap R K) := ⟨yK, hyK⟩

  let b : R →+* k := PowerSeries.constantCoeff
  have hba : b.comp a = Polynomial.evalRingHom 0 := by
    apply RingHom.ext
    intro f
    change PowerSeries.constantCoeff (f : PowerSeries k) = f.eval 0
    exact Polynomial.coeff_zero_eq_eval_zero f
  have hPb : P.map b = p := by
    change ((cubicPencil p q).map a).map b = p
    rw [MvPolynomial.map_map, hba, cubicPencil_map_eval_zero]
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
    rw [show IsLocalRing.maximalIdeal R = Ideal.span {PowerSeries.X} from
      PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  let _ : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hcomplete
  obtain ⟨yk, hyk⟩ := specialize_proper_point f b hpointK
  obtain ⟨v, hv, hev⟩ := hypersurface_coordinates_of_point b P hP yk hyk
  refine ⟨v, hv, ?_⟩
  have he : (P.map b).eval v = 0 := by
    rw [MvPolynomial.eval_map]
    exact hev
  rwa [hPb] at he

/-- The same pencil argument with the literal hypothesis of Chapter 6's
`prop:smoothing`: a smooth generic cubic with a degree-one zero-cycle has a
rational point.  Ma's degree-preserving lift is retained as an explicit
argument so this theorem does not conceal any external input. -/
theorem cubic_coordinates_of_smooth_extension_point_of_powerSeriesSmooth_ma
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (smoothGeneric : SmoothCubicZeroCyclePointFor (FractionRing (PowerSeries k)))
    (ma : MaCubicPencilPointLiftingFor k)
    (p q : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    (hqs : Smooth (hypersurfaceToBase q hq))
    (x : Fin 4 → L)
    (hx : IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) x)
    (hdegree : Nat.Coprime (Module.finrank k L) 3) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  let R := PowerSeries k
  let K := FractionRing R
  let a : Polynomial k →+* R := Polynomial.coeToPowerSeries.ringHom
  let g : Polynomial k →+* K := (algebraMap R K).comp a
  have hg : Function.Injective g :=
    (FaithfulSMul.algebraMap_injective R K).comp (Polynomial.coe_injective k)
  let _ : Smooth (hypersurfaceToBase q hq) := hqs
  have hgenericSmooth : Smooth
      (hypersurfaceToBase (powerSeriesPencilGeneric p q)
        (powerSeriesPencilGeneric_isHomogeneous hp hq)) := by
    exact cubicPencil_map_smooth g hg hp hq hq0
  let _ : Smooth
      (hypersurfaceToBase (powerSeriesPencilGeneric p q)
        (powerSeriesPencilGeneric_isHomogeneous hp hq)) := hgenericSmooth

  obtain ⟨z, hz⟩ := ma L p q hp hq x hx
  have hzcoprime : Nat.Coprime
      (EffectiveZeroCycle.degree
        (hypersurfaceToBase (powerSeriesPencilGeneric p q)
          (powerSeriesPencilGeneric_isHomogeneous hp hq)) z) 3 := by
    rw [hz]
    exact hdegree
  obtain ⟨w, hw⟩ := cubicSurface_zeroCycle_degree_one_of_effective_coprime
    (powerSeriesPencilGeneric p q)
    (powerSeriesPencilGeneric_isHomogeneous hp hq) z hzcoprime
  have hgeneric0 : powerSeriesPencilGeneric p q ≠ 0 := by
    change (cubicPencil p q).map g ≠ 0
    intro h
    apply cubicPencil_ne_zero_of_right hq0
    apply MvPolynomial.map_injective g hg
    simpa only [map_zero] using h
  obtain ⟨aK, haK⟩ := smoothGeneric (powerSeriesPencilGeneric p q)
    (powerSeriesPencilGeneric_isHomogeneous hp hq) hgeneric0 hgenericSmooth w hw
  obtain ⟨y, hy, hey⟩ := hypersurface_coordinates_of_point (RingHom.id K)
    (powerSeriesPencilGeneric p q) (powerSeriesPencilGeneric_isHomogeneous hp hq)
    aK (by simpa using haK)

  let P : MvPolynomial (Fin 4) R := (cubicPencil p q).map a
  have hP : P.IsHomogeneous 3 := (cubicPencil_isHomogeneous hp hq).map a
  have hPK : P.map (algebraMap R K) = powerSeriesPencilGeneric p q := by
    change ((cubicPencil p q).map a).map (algebraMap R K) = _
    rw [powerSeriesPencilGeneric, MvPolynomial.map_map]
  obtain ⟨yK, hyK⟩ := hypersurface_point_of_coordinates
    (algebraMap R K) P hP y hy (by
      rw [← MvPolynomial.eval_map, hPK]
      exact hey)
  let f := hypersurfaceToBase P hP
  have hpointK : HasPointOver f (algebraMap R K) := ⟨yK, hyK⟩

  let b : R →+* k := PowerSeries.constantCoeff
  have hba : b.comp a = Polynomial.evalRingHom 0 := by
    apply RingHom.ext
    intro f
    change PowerSeries.constantCoeff (f : PowerSeries k) = f.eval 0
    exact Polynomial.coeff_zero_eq_eval_zero f
  have hPb : P.map b = p := by
    change ((cubicPencil p q).map a).map b = p
    rw [MvPolynomial.map_map, hba, cubicPencil_map_eval_zero]
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
    rw [show IsLocalRing.maximalIdeal R = Ideal.span {PowerSeries.X} from
      PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  let _ : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hcomplete
  obtain ⟨yk, hyk⟩ := specialize_proper_point f b hpointK
  obtain ⟨v, hv, hev⟩ := hypersurface_coordinates_of_point b P hP yk hyk
  refine ⟨v, hv, ?_⟩
  have he : (P.map b).eval v = 0 := by
    rw [MvPolynomial.eval_map]
    exact hev
  rwa [hPb] at he

end AllCharacteristics
