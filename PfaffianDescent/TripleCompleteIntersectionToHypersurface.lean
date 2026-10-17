import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.TripleCompleteIntersectionHilbert
import AllCharacteristics.CyclePushforward
import AllCharacteristics.HomogeneousProjectiveAmbient

/-!
# Triple complete intersections inside a hypersurface

The three-equation complete intersection is an actual closed projective
subscheme of the hypersurface cut out by its first equation.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

section

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The first equation's homogeneous ideal is contained in the ideal of the
three-equation complete intersection. -/
theorem equationIdeal_le_tripleCompleteIntersectionIdeal
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c) :
    (equationIdeal f hf).toIdeal ≤
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal := by
  apply Ideal.span_le.mpr
  rintro x rfl
  exact Ideal.subset_span (by simp)

/-- The triple complete intersection maps to its first hypersurface as a
closed projective subscheme. -/
noncomputable def tripleCompleteIntersectionToHypersurface
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c) :
    scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) ⟶
      hypersurface f hf :=
  schemeQuotientMap (equationIdeal f hf)
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
    (equationIdeal_le_tripleCompleteIntersectionIdeal f g h hf hg hh)

instance tripleCompleteIntersectionToHypersurface_isClosedImmersion
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c) :
    IsClosedImmersion (tripleCompleteIntersectionToHypersurface f g h hf hg hh) := by
  exact schemeQuotientMap_closedImmersion (equationIdeal f hf)
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
    (equationIdeal_le_tripleCompleteIntersectionIdeal f g h hf hg hh)

/-- The complete-intersection immersion is over the coefficient field. -/
theorem tripleCompleteIntersectionToHypersurface_toBase
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c) :
    tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫ hypersurfaceToBase f hf =
      toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) := by
  exact schemeQuotientMap_toBase (equationIdeal f hf)
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
    (equationIdeal_le_tripleCompleteIntersectionIdeal f g h hf hg hh)

/-- Composing the canonical immersion of a three-equation intersection into
its first hypersurface with the ambient immersion is the canonical ambient
immersion of the complete intersection itself. -/
theorem tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c) :
    tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
      hypersurfaceToAmbient f hf =
    quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) := by
  unfold tripleCompleteIntersectionToHypersurface hypersurfaceToAmbient
    quotientProjMap schemeQuotientMap
  let F := quotientGradedRingHom (equationIdeal f hf)
  let G := gradedQuotientMap (equationIdeal f hf)
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
    (equationIdeal_le_tripleCompleteIntersectionIdeal f g h hf hg hh)
  have hGF : G.comp F =
      quotientGradedRingHom (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) := by
    ext x
    rfl
  have hcomp := Proj.map_comp F G
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal f hf))
    (gradedSurjective_irrelevant_le G
      (gradedQuotientMap_surjective (equationIdeal f hf)
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
        (equationIdeal_le_tripleCompleteIntersectionIdeal f g h hf hg hh)))
  calc
    _ = Proj.map G (gradedSurjective_irrelevant_le G
        (gradedQuotientMap_surjective (equationIdeal f hf)
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
          (equationIdeal_le_tripleCompleteIntersectionIdeal f g h hf hg hh))) ≫
        Proj.map F (irrelevant_le_map_quotientGradedRingHom (equationIdeal f hf)) := by rfl
    _ = Proj.map (G.comp F) (HomogeneousIdeal.irrelevant_le_map_comp
        (irrelevant_le_map_quotientGradedRingHom (equationIdeal f hf))
        (gradedSurjective_irrelevant_le G
          (gradedQuotientMap_surjective (equationIdeal f hf)
            (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
            (equationIdeal_le_tripleCompleteIntersectionIdeal f g h hf hg hh)))) := hcomp.symm
    _ = _ := by cases hGF; rfl

/-- A closed subscheme of the hypersurface factors through the selected
complete intersection as soon as its kernel contains the complete
intersection kernel.  This is the intrinsic scheme-theoretic expression of
the statement that the two additional equations vanish on that subscheme. -/
noncomputable def tripleCompleteIntersectionLift
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker) :
    Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) :=
  IsClosedImmersion.lift
    (tripleCompleteIntersectionToHypersurface f g h hf hg hh) i hker

/-- The intrinsic factorization is over the original hypersurface. -/
@[reassoc]
theorem tripleCompleteIntersectionLift_fac
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker) :
    tripleCompleteIntersectionLift f g h hf hg hh i hker ≫
        tripleCompleteIntersectionToHypersurface f g h hf hg hh = i :=
  IsClosedImmersion.lift_fac
    (tripleCompleteIntersectionToHypersurface f g h hf hg hh) i hker

/-- The factorization obtained from a kernel inclusion remains a closed
immersion. -/
instance tripleCompleteIntersectionLift_isClosedImmersion
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker) :
    IsClosedImmersion (tripleCompleteIntersectionLift f g h hf hg hh i hker) := by
  haveI : IsClosedImmersion
      (tripleCompleteIntersectionLift f g h hf hg hh i hker ≫
        tripleCompleteIntersectionToHypersurface f g h hf hg hh) := by
    rw [tripleCompleteIntersectionLift_fac]
    infer_instance
  exact IsClosedImmersion.of_comp _
    (tripleCompleteIntersectionToHypersurface f g h hf hg hh)

/-- An effective zero-cycle on a triple complete intersection pushes forward
to the first hypersurface without changing its degree over the coefficient
field. -/
theorem exists_effectiveZeroCycle_on_hypersurface_of_triple
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c)
    (n : ℕ)
    (r : AllCharacteristics.EffectiveZeroCycle
      (scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)))
    (hr : AllCharacteristics.EffectiveZeroCycle.degree
      (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) r = n) :
    ∃ s : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) s = n := by
  refine ⟨AllCharacteristics.pushforwardClosedCycle
    (tripleCompleteIntersectionToHypersurface f g h hf hg hh) r, ?_⟩
  rw [AllCharacteristics.degree_pushforwardClosedCycle,
    tripleCompleteIntersectionToHypersurface_toBase]
  exact hr

end

section

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- Evaluation at a point annihilates the ideal of a triple complete
intersection as soon as it annihilates its three defining equations. -/
theorem eval₂_vanishes_on_tripleCompleteIntersectionIdeal
    (f g h : MvPolynomial (Fin 4) K)
    (x : Fin 4 → A)
    (hf : f.eval₂ (algebraMap K A) x = 0)
    (hg : g.eval₂ (algebraMap K A) x = 0)
    (hh : h.eval₂ (algebraMap K A) x = 0) :
    ∀ s ∈ tripleCompleteIntersectionIdeal f g h,
      s.eval₂ (algebraMap K A) x = 0 := by
  have hker : tripleCompleteIntersectionIdeal f g h ≤
      RingHom.ker (eval₂Hom (algebraMap K A) x) := by
    rw [tripleCompleteIntersectionIdeal]
    apply Ideal.span_le.mpr
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hf
    · exact hg
    · exact hh
  exact fun s hs ↦ hker hs

end

end PfaffianDescent
