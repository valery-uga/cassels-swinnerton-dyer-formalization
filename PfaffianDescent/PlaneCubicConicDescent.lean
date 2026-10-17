import PfaffianDescent.ConicThroughFive
import PfaffianDescent.ConicCubicResidual
import PfaffianDescent.LinearFactorPoint
import PfaffianDescent.ProjectiveClosedPointCoordinates
import AllCharacteristics.ClosedPointAlgebra

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K A : Type u} [Field K] [Infinite K] [CommRing A] [Algebra K A]
    [Module.Finite K A]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The conic construction proves descent for a normalized length-five
closed point or subscheme on a plane cubic, including nonreduced algebras. -/
theorem plane_cubic_normalized_five_conic_descent
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous 3)
    (hA : finrank K A = 5) (x : Fin 3 → A) (j : Fin 3) (hx : x j = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x))
    (hfx : f.eval₂ (algebraMap K A) x = 0) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨q, hq0, hq, hqx⟩ := exists_conic_through_degree_five hA x
  by_cases hrel : IsRelPrime q f
  · let I := conicCubicHomogeneousIdeal q f hq hf
    have : IsFinite (toBase I) := conic_cubic_intersection_finite q f hq hf hq0 hrel
    have he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0 := by
      have hle : I.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K A) x) := by
        apply Ideal.span_le.mpr
        intro p hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp
        · exact hqx
        · obtain rfl := Set.mem_singleton_iff.mp hp
          exact hfx
      exact fun p hp => hle hp
    obtain ⟨i, hi, hbase⟩ := closed_point_of_normalized_coordinates I x j hx he hgen
    have hlen : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 5 := by
      rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hbase,
        Scheme.Hom.finrank_SpecMap_algebraMap]
      exact (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := A)) _).trans hA
    obtain ⟨s, hs⟩ := conic_cubic_residual_section q f hq hf hq0 hrel i hlen
    obtain ⟨v, hv, hev⟩ := homogeneous_coordinates_of_point I (RingHom.id K) s (by simpa using hs)
    have hfv : f.eval₂ (RingHom.id K) v = 0 :=
      hev f (Ideal.subset_span (Set.mem_insert_of_mem q (Set.mem_singleton f)))
    obtain ⟨t, ht⟩ := hypersurface_point_of_coordinates (RingHom.id K) f hf v hv hfv
    exact ⟨t, by simpa using ht⟩
  · exact conic_cubic_not_relPrime_section hq hf hq0 hrel

end

section
variable {K L : Type u} [Field K] [Infinite K] [Field L] [Algebra K L]
    [Module.Finite K L]

/-- The actual degree-five closed-point version of the elementary conic
argument on a plane cubic. Both the coprime and common-component cases are proved. -/
theorem plane_cubic_closed_point_conic_descent
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous 3)
    (hL : finrank K L = 5)
    (p : Spec (.of L) ⟶ hypersurface f hf) [IsClosedImmersion p]
    (hp : p ≫ hypersurfaceToBase f hf = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  let p' : Spec (.of L) ⟶ scheme (equationIdeal f hf) := p
  have : IsClosedImmersion p' := inferInstanceAs (IsClosedImmersion p)
  obtain ⟨j, x, hx, hgen, he⟩ := closed_projective_point_generating_coordinates
    (equationIdeal f hf) p' hp
  exact plane_cubic_normalized_five_conic_descent f hf hL x j hx hgen
    (he f (Ideal.subset_span (Set.mem_singleton f)))

end
end PfaffianDescent
