import AllCharacteristics.CubicSmoothing
import AllCharacteristics.HypersurfaceFiberCycles
import AllCharacteristics.HypersurfaceJacobianSmooth

/-!
# Ma's degree-preserving lifting step for a cubic pencil

This proves the precise instance of Ma's smooth-point lifting method used in
the cubic-surface argument.  A smooth point over an arbitrary finite residue
extension lifts through the power-series pencil to an effective cycle on the
generic fiber with exactly the same degree.  No separability or perfectness
hypothesis is used.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective

universe u

/-- Equality of homogeneous equations transports effective cycles without
changing their degree. -/
theorem exists_effectiveZeroCycle_hypersurface_of_eq
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    {r s : MvPolynomial σ R} {d : ℕ}
    (hr : r.IsHomogeneous d) (hs : s.IsHomogeneous d) (h : r = s)
    (z : EffectiveZeroCycle (hypersurface r hr)) :
    ∃ w : EffectiveZeroCycle (hypersurface s hs),
      EffectiveZeroCycle.degree (hypersurfaceToBase s hs) w =
        EffectiveZeroCycle.degree (hypersurfaceToBase r hr) z := by
  subst s
  exact ⟨z, rfl⟩

/-- Ma's smooth-point lifting input for the power-series cubic pencil is a
theorem over every field. -/
theorem maCubicPencilPointLiftingFor (k : Type u) [Field k] :
    MaCubicPencilPointLiftingFor k := by
  intro L _ _ _ p q hp hq x hx
  let R := PowerSeries k
  let K := FractionRing R
  let a : Polynomial k →+* R := Polynomial.coeToPowerSeries.ringHom
  let b : R →+* k := PowerSeries.constantCoeff
  let g : R →+* K := algebraMap R K
  let P : MvPolynomial (Fin 4) R := (cubicPencil p q).map a
  have hP : P.IsHomogeneous 3 := (cubicPencil_isHomogeneous hp hq).map a
  have hba : b.comp a = Polynomial.evalRingHom 0 := by
    apply RingHom.ext
    intro r
    change PowerSeries.constantCoeff (r : PowerSeries k) = r.eval 0
    exact Polynomial.coeff_zero_eq_eval_zero r
  have hPb : P.map b = p := by
    change ((cubicPencil p q).map a).map b = p
    rw [MvPolynomial.map_map, hba, cubicPencil_map_eval_zero]
  let bL : R →+* L := (algebraMap k L).comp b
  have he : P.eval₂ bL x = 0 := by
    change P.eval₂ ((algebraMap k L).comp b) x = 0
    rw [← MvPolynomial.eval₂_map, hPb]
    simpa only [MvPolynomial.eval_map] using hx.2.1
  have hd : ∃ i : Fin 4, (MvPolynomial.pderiv i P).eval₂ bL x ≠ 0 := by
    obtain ⟨i, hi⟩ := hx.2.2
    refine ⟨i, ?_⟩
    change (MvPolynomial.pderiv i P).eval₂ ((algebraMap k L).comp b) x ≠ 0
    rw [← MvPolynomial.eval₂_map, ← MvPolynomial.pderiv_map, hPb]
    simpa only [MvPolynomial.eval_map, MvPolynomial.pderiv_map] using hi
  obtain ⟨s, hs, hsm⟩ :=
    exists_hypersurface_point_mem_smoothLocus_of_pderiv
      P hP bL x hx.1 he hd
  let f := hypersurfaceToBase P hP
  have hcomplete : IsAdicComplete (maximalIdeal R) R := by
    rw [show maximalIdeal R = Ideal.span {PowerSeries.X} from
      PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  letI : IsAdicComplete (maximalIdeal R) R := hcomplete
  obtain ⟨zf, hzf⟩ :=
    exists_effectiveZeroCycle_fiber_of_finite_point_in_smoothLocus
      b PowerSeries.constantCoeff_surj f s hs hsm
      (Spec.map (CommRingCat.ofHom g))
  obtain ⟨z, hz⟩ :=
    exists_effectiveZeroCycle_mapped_of_fiber_cycle P hP g zf
  have hPK : P.map g = powerSeriesPencilGeneric p q := by
    change ((cubicPencil p q).map a).map (algebraMap R K) = _
    rw [powerSeriesPencilGeneric, MvPolynomial.map_map]
  obtain ⟨w, hw⟩ := exists_effectiveZeroCycle_hypersurface_of_eq
    (hP.map g) (powerSeriesPencilGeneric_isHomogeneous hp hq) hPK z
  exact ⟨w, hw.trans (hz.trans hzf)⟩

/- The proved lifting instance can be inlined into the smooth-extension
reduction, so callers need not carry Ma's statement as an extra hypothesis. -/
theorem cubic_coordinates_of_smooth_extension_point_of_voisin
    (voisin : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeOneOrFourFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p q : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    (hqs : Smooth (hypersurfaceToBase q hq))
    (x : Fin 4 → L)
    (hx : IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) x)
    (hdegree : Nat.Coprime (Module.finrank k L) 3) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  cubic_coordinates_of_smooth_extension_point_of_voisin_ma
    voisin (maCubicPencilPointLiftingFor k) p q hp hq hq0 hqs x hx hdegree

end AllCharacteristics
