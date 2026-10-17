import PfaffianDescent.IndependentConicInterpolation
import PfaffianDescent.IndependentClosedPointQuotientFactor
import PfaffianDescent.ConicCubicLength
import PfaffianDescent.LinearFactorPoint
import PfaffianDescent.FiniteClosedSubschemeCycleComplement
import AllCharacteristics.SchemeQuadraticDescent
import AllCharacteristics.ClosedPointAlgebra

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual finite conic/cubic intersection maps to its original cubic. -/
noncomputable def conicCubicToPlaneCubic
    {K : Type u} [Field K] (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) :
    scheme (conicCubicHomogeneousIdeal q f hq hf) ⟶ hypersurface f hf :=
  schemeQuotientMap (equationIdeal f hf) (conicCubicHomogeneousIdeal q f hq hf)
    (by
      apply Ideal.span_le.mpr
      intro a ha
      have haf : a = f := Set.mem_singleton_iff.mp ha
      subst a
      exact Ideal.subset_span (Set.mem_insert_of_mem q (Set.mem_singleton f)))

instance conicCubicToPlaneCubic_isClosedImmersion
    {K : Type u} [Field K] (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) :
    IsClosedImmersion (conicCubicToPlaneCubic q f hq hf) :=
  schemeQuotientMap_closedImmersion _ _ _

theorem conicCubicToPlaneCubic_toBase
    {K : Type u} [Field K] (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) :
    conicCubicToPlaneCubic q f hq hf ≫ hypersurfaceToBase f hf =
      toBase (conicCubicHomogeneousIdeal q f hq hf) :=
  schemeQuotientMap_toBase _ _ _

/-- Subtracting the SAME embedded length-four subscheme from the full length-six
intersection produces an effective degree-two complement, retaining nilpotent
scheme lengths. This does not assert an annihilator residual is Frobenius. -/
theorem conic_cubic_quartic_complement_cycle
    {K : Type u} [Field K] [Infinite K]
    (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f)
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (conicCubicHomogeneousIdeal q f hq hf)) [IsClosedImmersion i]
    (hZ : letI := conic_cubic_intersection_finite q f hq hf hq0 hrel
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (conicCubicHomogeneousIdeal q f hq hf)) = 4) :
    ∃ z : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 2 := by
  let I := conicCubicHomogeneousIdeal q f hq hf
  let c := conicCubicToPlaneCubic q f hq hf
  letI : IsFinite (toBase I) := conic_cubic_intersection_finite q f hq hf hq0 hrel
  have hbase : c ≫ hypersurfaceToBase f hf = toBase I :=
    conicCubicToPlaneCubic_toBase q f hq hf
  letI : IsFinite (c ≫ hypersurfaceToBase f hf) := by
    rw [hbase]
    infer_instance
  have hW : AllCharacteristics.finiteSchemeRank (c ≫ hypersurfaceToBase f hf) = 6 := by
    simpa only [hbase] using conic_cubic_intersection_length_six q f hq hf hq0 hrel
  have hZ' : AllCharacteristics.finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase f hf) = 4 := by
    simpa only [Category.assoc, hbase] using hZ
  obtain ⟨z, hz⟩ := exists_effectiveCycle_of_finite_closed_subscheme_rank_difference
    i c (hypersurfaceToBase f hf) 6 4 hW hZ'
  exact ⟨z, by simpa using hz⟩

/-- Independent Chapter 2 conic/secant argument for the exact given closed
quartic point of a plane cubic. Common components supply a ground line. -/
theorem plane_cubic_closed_quartic_conic_secant_descent
    {K L : Type u} [Field K] [Infinite K] [Field L] [Algebra K L]
    [Module.Finite K L]
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous 3)
    (hL : finrank K L = 4)
    (p : Spec (.of L) ⟶ hypersurface f hf) [IsClosedImmersion p]
    (hp : p ≫ hypersurfaceToBase f hf = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf,
      s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨j, g, _, hgbase, hgpoint⟩ := closed_projective_point_chart (equationIdeal f hf) p hp
  let x : Fin 3 → L := fun k => g (chartCoordinate (equationIdeal f hf) j k)
  obtain ⟨q, hq0, hq, hqx⟩ := exists_conic_through_algebra_finrank_lt_six
    (by omega : finrank K L < 6) x
  by_cases hrel : IsRelPrime q f
  · let I := conicCubicHomogeneousIdeal q f hq hf
    have hIJ : (equationIdeal f hf).toIdeal ≤ I.toIdeal := by
      apply Ideal.span_le.mpr
      intro a ha
      have haf : a = f := Set.mem_singleton_iff.mp ha
      subst a
      exact Ideal.subset_span (Set.mem_insert_of_mem q (Set.mem_singleton f))
    have hfx : f.eval₂ (algebraMap K L) x = 0 := by
      change f.eval₂ (algebraMap K L)
        (fun k => g (chartCoordinate (equationIdeal f hf) j k)) = 0
      rw [← hgbase, ← hom_eval₂,
        eval₂_chartCoordinate_eq_zero_of_mem (equationIdeal f hf) j f
          (Ideal.subset_span (Set.mem_singleton f)), map_zero]
    have hI : ∀ r ∈ I.toIdeal, r.eval₂ (algebraMap K L) x = 0 := by
      have hle : I.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K L) x) := by
        apply Ideal.span_le.mpr
        intro r hr
        rcases Set.mem_insert_iff.mp hr with rfl | hr
        · exact hqx
        · obtain rfl := Set.mem_singleton_iff.mp hr
          exact hfx
      exact fun r hr => hle hr
    obtain ⟨i, hi, hfactor, hbase⟩ :=
      closed_field_point_factor_through_homogeneous_quotient
        (equationIdeal f hf) I hIJ p hp j g hgbase hgpoint hI
    letI : IsClosedImmersion i := hi
    letI : IsFinite (toBase I) := conic_cubic_intersection_finite q f hq hf hq0 hrel
    have hlen : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 4 := by
      rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hbase,
        Scheme.Hom.finrank_SpecMap_algebraMap]
      exact (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := L)) _).trans hL
    -- hfactor identifies this i with the exact original p after forgetting q.
    have hsame : i ≫ conicCubicToPlaneCubic q f hq hf = p := hfactor
    obtain ⟨z, hz⟩ := conic_cubic_quartic_complement_cycle q f hq hf hq0 hrel i hlen
    exact hypersurface_section_of_effective_cycle_degree_one_or_two f hf z (Or.inr hz)
  · exact conic_cubic_not_relPrime_section hq hf hq0 hrel

/-- Actual residue-point formulation, without coordinate/frame certificates. -/
theorem plane_cubic_residue_degree_four_conic_secant_descent
    {K : Type u} [Field K] [Infinite K]
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous 3)
    (x : closedPoints (hypersurface f hf))
    (hx : (hypersurfaceToBase f hf).residueDegree x.1 = 4) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf,
      s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase f hf) x.1
  have := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase f hf) x
  letI : IsClosedImmersion ((hypersurface f hf).fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp x.2
  have hd := (AllCharacteristics.closedPoint_finrank_eq_residueDegree
    (hypersurfaceToBase f hf) x).trans hx
  exact plane_cubic_closed_quartic_conic_secant_descent f hf hd
    ((hypersurface f hf).fromSpecResidueField x.1)
    (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase f hf) x.1).symm

end PfaffianDescent
