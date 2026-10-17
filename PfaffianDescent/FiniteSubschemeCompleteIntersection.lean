import PfaffianDescent.FiniteProjectiveNormalizedCoordinates
import PfaffianDescent.NormalizedProjectiveQuotientFactor
import PfaffianDescent.TripleCompleteIntersectionHilbert
import AllCharacteristics.HomogeneousProjectiveAmbient

/-!
# Finite subschemes inside three-equation complete intersections

This is the scheme-theoretic bridge used in Voisin's residual constructions.
Normalized homogeneous coordinates of a finite subscheme can be reused after
adding two further equations that vanish on those coordinates.  The resulting
map is an actual closed immersion into the corresponding projective complete
intersection, not only a statement about sets of points.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Generating projective coordinates normalized by a linear form and
satisfying three homogeneous equations define a closed immersion into their
scheme-theoretic complete intersection. -/
theorem closed_point_of_triple_complete_intersection_coordinates
    (f g h : MvPolynomial (Fin 4) K) {a b c : ℕ}
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b)
    (hh : h.IsHomogeneous c)
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (hxell : ell.eval₂ (algebraMap K A) x = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x))
    (hfx : f.eval₂ (algebraMap K A) x = 0)
    (hgx : g.eval₂ (algebraMap K A) x = 0)
    (hhx : h.eval₂ (algebraMap K A) x = 0) :
    ∃ j : Spec (.of A) ⟶
        scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh),
      IsClosedImmersion j ∧
        j ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) =
          Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  let e : MvPolynomial (Fin 4) K →+* A := eval₂Hom (algebraMap K A) x
  have he : ∀ q ∈ (tripleCompleteIntersectionHomogeneousIdeal
      f g h hf hg hh).toIdeal, q.eval₂ (algebraMap K A) x = 0 := by
    intro q hq
    change e q = 0
    apply (show (tripleCompleteIntersectionIdeal f g h) ≤ RingHom.ker e by
      apply Ideal.span_le.mpr
      intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl
      · exact hfx
      · exact hgx
      · exact hhx) hq
  exact closed_point_of_linear_normalized_coordinates
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
    x ell hell hxell he hgen

end

section
variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite closed subscheme of a cubic surface admits generating
coordinates together with the ground-field linear form that normalizes them.
The surface equation vanishes on these same coordinates. -/
theorem cubicFiniteSubscheme_normalized_coordinates
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧
      ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  let j : Z ⟶ scheme (equationIdeal p hp) := i
  haveI : IsClosedImmersion j := ‹IsClosedImmersion i›
  haveI : IsFinite (j ≫ toBase (equationIdeal p hp)) := by
    change IsFinite (i ≫ hypersurfaceToBase p hp)
    infer_instance
  obtain ⟨x, ell, hx, hell, hxell, hvanish⟩ :=
    finite_projective_closed_subscheme_normalized_coordinates
      (equationIdeal p hp) j
  refine ⟨x, ell, hx, hell, hxell, ?_⟩
  exact hvanish p 3 hp (Ideal.subset_span (Set.mem_singleton p))

/-- A finite closed subscheme of a cubic surface has a normalized projective
chart which recovers its actual immersion into the surface.  Keeping this
chart, rather than only its coordinate functions, is what allows subsequent
vanishing cubics to define a complete-intersection embedding of the same
finite subscheme. -/
theorem cubicFiniteSubscheme_normalized_chart
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (z : CoordinateRing (equationIdeal p hp))
      (hz : z ∈ grading (equationIdeal p hp) 1)
      (x : Fin 4 → Γ(Z, ⊤))
      (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
        (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) s = 0)
      (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
        (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) he) z = 1),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
        Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  let j : Z ⟶ scheme (equationIdeal p hp) := i
  haveI : IsClosedImmersion j := ‹IsClosedImmersion i›
  haveI : IsFinite (j ≫ toBase (equationIdeal p hp)) := by
    change IsFinite (i ≫ hypersurfaceToBase p hp)
    infer_instance
  obtain ⟨z, hz, g, hgs, hbase, hdiag, ell, hell, hellz, x, hx,
    hxsurj, hxell, he, hzOne, hpoint⟩ :=
    finite_projective_closed_subscheme_normalized_chart (equationIdeal p hp) j
  have hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 := by
    exact he p (Ideal.subset_span (Set.mem_singleton p))
  refine ⟨z, hz, x, he, hzOne, hxsurj, hpx, ?_⟩
  change linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
    Z.isoSpec.inv ≫ j
  exact hpoint

/-- A finite closed subscheme of a cubic also admits a normalized chart in
the ambient projective space, represented by an actual linear form.  The
ambient normalized point is exactly the original immersion followed by the
cubic hypersurface embedding. -/
theorem cubicFiniteSubscheme_normalized_ambient_chart
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] :
    letI : IsAffine Z := isAffine_of_isAffineHom
      (i ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra
      (i ≫ hypersurfaceToBase p hp)
    ∃ (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
      (x : Fin 4 → Γ(Z, ⊤))
      (he₀ : ∀ q ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) K)).toIdeal,
        (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) q = 0)
      (hellOne : (Ideal.Quotient.lift
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal
        (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) he₀)
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) K)).toIdeal ell) = 1),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
      linearNormalizedPointAt
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
          x he₀
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) K)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
            ell hell) hellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) =
        Z.isoSpec.inv ≫ i ≫ hypersurfaceToAmbient p hp := by
  letI : IsAffine Z := isAffine_of_isAffineHom
    (i ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (i ≫ hypersurfaceToBase p hp)
  obtain ⟨w, hw, x, heJ, hwOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_chart p hp i
  obtain ⟨ell, hell, hellw⟩ := hw
  change Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell = w at hellw
  subst w
  have hellEval : ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 := by
    change (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ell = 1 at hwOne
    exact hwOne
  let I₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) K) := ⊥
  let J := equationIdeal p hp
  let he₀ : ∀ q ∈ I₀.toIdeal,
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) q = 0 := by
    intro q hq
    have hq0 : q = 0 := Ideal.mem_bot.mp hq
    subst q
    exact map_zero _
  let z₀ : CoordinateRing I₀ := Ideal.Quotient.mk I₀.toIdeal ell
  have hz₀ : z₀ ∈ grading I₀ 1 :=
    polynomial_class_mem_grading I₀ ell hell
  have hz₀One : (Ideal.Quotient.lift I₀.toIdeal
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) he₀) z₀ = 1 := by
    change (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ell = 1
    exact hellEval
  let hIJ : I₀.toIdeal ≤ J.toIdeal := bot_le
  have hzJOne : (Ideal.Quotient.lift J.toIdeal
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) heJ)
        (gradedQuotientMap I₀ J hIJ z₀) = 1 := by
    change (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ell = 1
    exact hellEval
  have hfactor :
      linearNormalizedPointAt J x heJ
          (gradedQuotientMap I₀ J hIJ z₀)
          ((gradedQuotientMap I₀ J hIJ).map_mem hz₀) hzJOne ≫
        schemeQuotientMap I₀ J hIJ =
      linearNormalizedPointAt I₀ x he₀ z₀ hz₀ hz₀One := by
    exact linearNormalizedPointAt_comp_schemeQuotientMap
      I₀ J hIJ x he₀ heJ z₀ hz₀ hz₀One hzJOne
  have hpoint' : linearNormalizedPointAt J x heJ
        (gradedQuotientMap I₀ J hIJ z₀)
        ((gradedQuotientMap I₀ J hIJ).map_mem hz₀) hzJOne =
      Z.isoSpec.inv ≫ i := by
    convert hpoint using 1 <;> try rfl
  refine ⟨ell, hell, x, he₀, hz₀One, hxsurj, hpx, ?_⟩
  calc
    linearNormalizedPointAt I₀ x he₀ z₀ hz₀ hz₀One ≫
        quotientProjMap I₀ =
      (linearNormalizedPointAt J x heJ
          (gradedQuotientMap I₀ J hIJ z₀)
          ((gradedQuotientMap I₀ J hIJ).map_mem hz₀) hzJOne ≫
        schemeQuotientMap I₀ J hIJ) ≫ quotientProjMap I₀ := by
          exact congrArg (fun t ↦ t ≫ quotientProjMap I₀) hfactor.symm
    _ = linearNormalizedPointAt J x heJ
          (gradedQuotientMap I₀ J hIJ z₀)
          ((gradedQuotientMap I₀ J hIJ).map_mem hz₀) hzJOne ≫
        quotientProjMap J := by
          rw [Category.assoc, schemeQuotientMap_comp_quotientProjMap]
    _ = (Z.isoSpec.inv ≫ i) ≫ quotientProjMap J := by
          exact congrArg (fun t ↦ t ≫ quotientProjMap J) hpoint'
    _ = _ := by exact rfl

end

end PfaffianDescent
