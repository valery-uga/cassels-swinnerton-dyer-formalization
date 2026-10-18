import AllCharacteristics.SmoothCubicJacobianProjectiveEmpty
import AllCharacteristics.HypersurfaceJacobianSmooth
import AllCharacteristics.SurjectiveResiduePresentation
import AllCharacteristics.ProjectivePoints
import AllCharacteristics.FieldParameterResidue

/-!
Derive ambient smoothness and relative surface dimension from the nonzero
smooth special cubic equation. Smoothness and relative dimension of the
lifted cubic are conclusions, rather than additional assumptions.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective IsLocalRing
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Empty equation-plus-partials Proj gives the retained-partial unit ideal
on each normalized cubic chart over an arbitrary commutative base ring.
The maximal-chart-ideal/Euler proof works without the base being a field. -/
theorem cubicJacobian_empty_chartPDeriv_span_top001
    {R : Type u} [CommRing R]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    (hempty : IsEmpty (scheme (cubicJacobianIdeal p hp))) :
    ∀ j : Fin 4, Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤ := by
  classical
  intro j
  by_contra hspan
  let I := equationIdeal p hp
  let D : Ideal (ChartRing I j) := Ideal.span (Set.range (chartPDeriv p hp j))
  obtain ⟨Q, hQ, hDQ⟩ := Ideal.exists_le_maximal D hspan
  letI : Q.IsMaximal := hQ
  let L := ChartRing I j ⧸ Q
  letI : Field L := Ideal.Quotient.field Q
  let e : ChartRing I j →+* L := Ideal.Quotient.mk Q
  let f : R →+* L := e.comp (chartBaseMap I j)
  let y : Fin 4 → L := fun a => e (chartCoordinate I j a)
  have hyj : y j = 1 := by simp only [y, chartCoordinate_self, map_one]
  have hy : y ≠ 0 := by
    intro hzero
    have hz := congrFun hzero j
    exact one_ne_zero (by simpa only [hyj, Pi.zero_apply] using hz)
  have hey : p.eval₂ f y = 0 := by
    have hz := congrArg e (eval₂_chartCoordinate_eq_zero I j p hp
      (Ideal.subset_span (Set.mem_singleton p)))
    rw [MvPolynomial.hom_eval₂, map_zero] at hz
    exact hz
  have hret : ∀ a : Fin 4, a ≠ j → (pderiv a p).eval₂ f y = 0 := by
    intro a haj
    have hmem : chartPDeriv p hp j ⟨a, haj⟩ ∈ Q :=
      hDQ (Ideal.subset_span ⟨⟨a, haj⟩, rfl⟩)
    have hz : e (chartPDeriv p hp j ⟨a, haj⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    change e ((pderiv a p).eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0 at hz
    rw [MvPolynomial.hom_eval₂] at hz
    exact hz
  have heuler : (∑ a : Fin 4, y a * (pderiv a p).eval₂ f y) = 0 := by
    calc
      (∑ a : Fin 4, y a * (pderiv a p).eval₂ f y) =
          (∑ a : Fin 4, X a * pderiv a p).eval₂ f y := by simp
      _ = (3 • p).eval₂ f y := by rw [hp.sum_X_mul_pderiv]
      _ = 0 := by simp [hey]
  have hsum : (∑ a : Fin 4, y a * (pderiv a p).eval₂ f y) =
      y j * (pderiv j p).eval₂ f y := by
    apply Finset.sum_eq_single j
    · intro a _ haj
      rw [hret a haj, mul_zero]
    · simp
  have hj : (pderiv j p).eval₂ f y = 0 := by
    rw [hsum, hyj, one_mul] at heuler
    exact heuler
  have hderiv : ∀ a : Fin 4, (pderiv a p).eval₂ f y = 0 := by
    intro a
    by_cases haj : a = j
    · simpa only [haj] using hj
    · exact hret a haj
  let J := cubicJacobianIdeal p hp
  have hI : I.toIdeal ≤ RingHom.ker (MvPolynomial.eval₂Hom f y) := by
    apply Ideal.span_le.mpr
    rintro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact hey
  have hpartials : ∀ a : Fin 4,
      (equationIdeal (pderiv a p) hp.pderiv).toIdeal ≤
        RingHom.ker (MvPolynomial.eval₂Hom f y) := by
    intro a
    apply Ideal.span_le.mpr
    rintro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact hderiv a
  have hJ : J.toIdeal ≤ RingHom.ker (MvPolynomial.eval₂Hom f y) := by
    simp only [J, cubicJacobianIdeal, HomogeneousIdeal.toIdeal_sup,
      HomogeneousIdeal.toIdeal_iSup]
    exact sup_le hI (iSup_le hpartials)
  obtain ⟨q, hq⟩ := point_of_coordinates J f y hy (fun a ha => hJ ha)
  letI : IsEmpty (scheme J) := hempty
  exact isEmptyElim (q (IsLocalRing.closedPoint L))

/-- The specified surjection really sends the unique field point to the
closed point of the original local ring. -/
private theorem surjectiveFieldPoint_eq_originalClosedPoint001
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) :
    Spec.map (CommRingCat.ofHom b) (closedPoint k) = closedPoint R := by
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap b (closedPoint k)).asIdeal = maximalIdeal R
  exact (fieldPoint_asIdeal_eq_ker b).trans (ker_eq_maximalIdeal b hb)

/-- The actual TOTAL equation-plus-partials scheme is empty because its
proper image is closed and misses the original local closed point.  The
special equation and its nonzero/smooth hypotheses are the manuscript's
inputs; no assertion about a lifted surface is supplied as a premise. -/
theorem originalLocalCubicJacobian_isEmpty_of_smooth_nonzero_reduction001
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) R) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) (he : q.map b = p)
    [Smooth (hypersurfaceToBase p hp)] :
    IsEmpty (scheme (cubicJacobianIdeal q hq)) := by
  let I := cubicJacobianIdeal q hq
  let J := cubicJacobianIdeal p hp
  have hmap : I.toIdeal.map (MvPolynomial.map b) = J.toIdeal := by
    have h := cubicJacobianIdeal_map b q hq
    simpa only [I, J, he] using h
  let e := projectiveBaseChangeIso b I J hmap
  letI : IsEmpty (scheme J) := smoothCubic_cubicJacobianScheme_isEmpty p hp hp0
  have hclosed : IsClosed (Set.range (toBase I)) :=
    cubicJacobianProjection_range_isClosed q hq
  have hmiss : closedPoint R ∉ Set.range (toBase I) := by
    intro hmem
    have hfield : Spec.map (CommRingCat.ofHom b) (closedPoint k) ∈
        Set.range (toBase I) := by
      rwa [surjectiveFieldPoint_eq_originalClosedPoint001 b hb]
    have hpre : closedPoint k ∈
        Set.range (pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom b))) := by
      rw [Scheme.Pullback.range_snd]
      exact hfield
    obtain ⟨z, _⟩ := hpre
    exact isEmptyElim (e.inv z)
  refine ⟨fun x => ?_⟩
  exact hmiss ((specializes_closedPoint (toBase I x)).mem_closed hclosed
    (Set.mem_range_self x))

/-- The lifted cubic is a genuine smooth RELATIVE SURFACE.  This derives
relative dimension two from the original nonzero smooth special equation,
even over an arbitrary local base.  No DVR/completeness/dimension outcome
is needed as a premise. -/
theorem originalLocalCubic_smoothOfRelativeDimension_two_of_reduction001
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) R) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) (he : q.map b = p)
    [Smooth (hypersurfaceToBase p hp)] :
    SmoothOfRelativeDimension 2 (hypersurfaceToBase q hq) :=
  smoothOfRelativeDimension_two_hypersurface_of_chart_pderiv_span q hq
    (cubicJacobian_empty_chartPDeriv_span_top001 q hq
      (originalLocalCubicJacobian_isEmpty_of_smooth_nonzero_reduction001
        b hb q hq p hp hp0 he))

end PfaffianDescent
end
