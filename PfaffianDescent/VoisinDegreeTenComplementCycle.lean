import PfaffianDescent.VoisinFiniteSubschemeDatumResidual
import PfaffianDescent.VoisinDegreeTenSmoothStart

/-!
# The cycle complement in Voisin's first degree-ten residual

For the effective-cycle conclusion of the first `16 → 11` step, a proper
intersection of three cubics suffices.  The degree-eleven cycle is the
complement of the completed finite subscheme in the length-twenty-seven
intersection.  This does not require the intersection to be reduced or étale.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem finiteSchemeFundamentalCycle_eq_of_baseMaps
    {Z : Scheme.{u}} (f g : Z ⟶ Spec (.of K)) [IsFinite f] [IsFinite g] :
    finiteSchemeFundamentalCycle f = finiteSchemeFundamentalCycle g := by
  ext x
  rw [finiteSchemeFundamentalCycle_apply, finiteSchemeFundamentalCycle_apply]

private theorem pushforwardClosedCycle_eq_of_hom_eq
    {Z X : Scheme.{u}} (i j : Z ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (h : i = j) (z : EffectiveZeroCycle Z) :
    pushforwardClosedCycle i z = pushforwardClosedCycle j z := by
  unfold pushforwardClosedCycle
  congr 1
  funext x
  apply Subtype.ext
  exact congrArg (fun g : Z ⟶ X => g x.val) h

private theorem finiteSubschemeDatumCycle_eq_pushforwardClosedCycle
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (D : FiniteSubschemeDatum f 16) :
    letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
    finiteSubschemeDatumCycle f D =
      pushforwardClosedCycle D.val.subschemeι
        (finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f)) := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  change pushforwardCycle D.val.subschemeι
    (finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f)) = _
  exact pushforwardCycle_eq_pushforwardClosedCycle _ _

/-- The complement identity remains an exact equality of effective cycles
after both finite schemes are pushed into the ambient surface. -/
theorem finiteClosedSubschemeComplementCycle_pushforward_add
    {Z W X : Scheme.{u}}
    (j : Z ⟶ W) [IsClosedImmersion j]
    (c : W ⟶ X) [IsClosedImmersion c]
    (f : X ⟶ Spec (.of K)) [IsFinite (c ≫ f)] :
    pushforwardClosedCycle c (finiteSchemeFundamentalCycle (c ≫ f)) =
      pushforwardClosedCycle c
          (finiteClosedSubschemeComplementCycle j (c ≫ f)) +
        pushforwardClosedCycle (j ≫ c)
          (finiteSchemeFundamentalCycle (j ≫ c ≫ f)) := by
  have h := congrArg (pushforwardClosedCycle c)
    (finiteClosedSubschemeComplementCycle_add j (c ≫ f))
  simp only [pushforwardClosedCycle, Finsupp.mapDomain_add] at h ⊢
  rw [← Finsupp.mapDomain_comp] at h
  convert h using 1
  congr 1

/-- The first complete intersection cycle is exactly the completed
rank-sixteen cycle plus an effective degree-eleven complement on the cubic.
This equality is at the level of effective cycles, before passing to Chow
classes. -/
theorem finiteSubschemeDatum_degree_sixteen_complement_cycle_add_of_completeIntersectionEmbedding
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (j : D.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      D.val.subschemeι) :
    let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
    let f := hypersurfaceToBase p hp
    letI : IsFinite (c ≫ f) := by
      rw [tripleCompleteIntersectionToHypersurface_toBase]
      exact triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree f z = 11 ∧
      pushforwardClosedCycle c (finiteSchemeFundamentalCycle (c ≫ f)) =
        z + finiteSubschemeDatumCycle f D := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  have hW : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, I, tripleCompleteIntersectionToHypersurface_toBase] using
      triple_cubic_intersection_length_twenty_seven
        p q r hp hq hr hne hq0 hrel hregular
  have hjbase : j ≫ c ≫ f = D.val.subschemeι ≫ f := by
    rw [← Category.assoc, hj]
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  let z : EffectiveZeroCycle (hypersurface p hp) :=
    pushforwardClosedCycle c
      (finiteClosedSubschemeComplementCycle j (c ≫ f))
  have hdegree : EffectiveZeroCycle.degree f z = 11 := by
    calc
      EffectiveZeroCycle.degree f z =
          finiteSchemeRank (c ≫ f) - finiteSchemeRank (j ≫ c ≫ f) := by
        rw [show EffectiveZeroCycle.degree f z =
            EffectiveZeroCycle.degree (c ≫ f)
              (finiteClosedSubschemeComplementCycle j (c ≫ f)) by
          exact degree_pushforwardClosedCycle c f _]
        exact finiteClosedSubschemeComplementCycle_degree j (c ≫ f)
      _ = 11 := by rw [hW, hZ]
  have hD : pushforwardClosedCycle (j ≫ c)
      (finiteSchemeFundamentalCycle (j ≫ c ≫ f)) =
      finiteSubschemeDatumCycle f D := by
    calc
      _ = pushforwardClosedCycle (j ≫ c)
          (finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f)) :=
        congrArg _ (finiteSchemeFundamentalCycle_eq_of_baseMaps (j ≫ c ≫ f)
          (D.val.subschemeι ≫ f))
      _ = pushforwardClosedCycle D.val.subschemeι
          (finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f)) :=
        pushforwardClosedCycle_eq_of_hom_eq (j ≫ c) D.val.subschemeι hj _
      _ = finiteSubschemeDatumCycle f D :=
        (finiteSubschemeDatumCycle_eq_pushforwardClosedCycle f D).symm
  refine ⟨z, hdegree, ?_⟩
  simpa only [z, hD] using
    finiteClosedSubschemeComplementCycle_pushforward_add j c f

/-- A normalized rank-sixteen subscheme in a proper triple-cubic
intersection leaves an effective degree-eleven cycle on the cubic surface. -/
theorem cubicFiniteSubscheme_degree_sixteen_complement_cycle_degree_eleven_of_selected_coordinates
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 16)
    (coordinates : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧
        ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom
    (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩ := coordinates
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx hqvan hrvan
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let j : Z ⟶ scheme I := Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase I = i ≫ hypersurfaceToBase p hp := by
    dsimp [j, I]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Z.isoSpec.hom_inv_id_assoc]
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ toBase I) = 16 := by
    simpa only [hjbase] using hi
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hW : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, I, tripleCompleteIntersectionToHypersurface_toBase] using
      triple_cubic_intersection_length_twenty_seven
        p q r hp hq hr hne hq0 hrel hregular
  have hZ' : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, I, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hZ
  exact exists_effectiveCycle_of_finite_closed_subscheme_rank_difference
    j c f 27 16 hW hZ'

/-- The finite-subscheme datum version of the proper-intersection
`16 → 11` cycle complement. -/
theorem finiteSubschemeDatum_degree_sixteen_complement_cycle_degree_eleven_of_selected_coordinates
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
        (ell : MvPolynomial (Fin 4) K),
        Function.Surjective
          (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧
        ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  let i : D.val.subscheme ⟶ hypersurface p hp := D.val.subschemeι
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ hypersurfaceToBase p hp) := by
    change IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    exact D.property.1
  have hi : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 16 := by
    rw [finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint K)
  exact cubicFiniteSubscheme_degree_sixteen_complement_cycle_degree_eleven_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular i hi coordinates

/-- The selected rank drop supplies a regular third cubic and an exact
effective-cycle identity for its intersection with the first two cubics. -/
theorem exists_degreeTenComplementCycle_with_identity_of_selectedFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenRegularCubicSectionSelectedFinrankDrop p hp D₁₀ S) :
    ∃ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3)
        (hregular : ∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))),
      ∃ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 ∧
        let c := tripleCompleteIntersectionToHypersurface
          p S.q r hp S.hq hr
        let f := hypersurfaceToBase p hp
        letI : IsFinite (c ≫ f) := by
          rw [tripleCompleteIntersectionToHypersurface_toBase]
          exact triple_cubic_intersection_finite
            p S.q r hp S.hq hr hne S.hq0 S.hrel hregular
        pushforwardClosedCycle c (finiteSchemeFundamentalCycle (c ≫ f)) =
          z + finiteSubschemeDatumCycle f S.completion.datum := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, hselected⟩ :=
    by simpa only [D] using hdrop
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop p S.q x
      (by simpa only [D] using hselected)
  have chart :
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI : IsAffine D.val.subscheme :=
        isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      letI := finiteSchemeCoefficientAlgebra
        (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (z : CoordinateRing (equationIdeal p hp))
        (hz : z ∈ grading (equationIdeal p hp) 1)
        (x : Fin 4 → Γ(D.val.subscheme, ⊤))
        (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
          (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) s = 0)
        (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
          (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) he) z = 1),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        S.q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
          D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι := by
    exact ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hrvan, hpoint⟩
  let j : D.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal
        p S.q r hp S.hq hr) :=
    finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart
      p S.q r hp S.hq hr 16 D chart
  letI : IsClosedImmersion j :=
    finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart_isClosedImmersion
      p S.q r hp S.hq hr 16 D chart
  have hj : j ≫ tripleCompleteIntersectionToHypersurface
      p S.q r hp S.hq hr = D.val.subschemeι :=
    finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart_fac
      p S.q r hp S.hq hr 16 D chart
  obtain ⟨z₁₁, hdegree, hcycle⟩ :=
    finiteSubschemeDatum_degree_sixteen_complement_cycle_add_of_completeIntersectionEmbedding
      p S.q r hp S.hq hr hne S.hq0 S.hrel hregular D j hj
  exact ⟨r, hr, hregular, z₁₁, hdegree, hcycle⟩

/-- The selected rank-drop condition yields an effective degree-eleven
cycle. The regular third cubic need not give a reduced intersection. -/
theorem exists_degreeTenComplementCycle_of_regularCubicSectionEmbeddingData_of_selectedFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenRegularCubicSectionSelectedFinrankDrop p hp D₁₀ S) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  obtain ⟨r, hr, hregular, z, hz, _⟩ :=
    exists_degreeTenComplementCycle_with_identity_of_selectedFinrankDrop
      p hp hne D₁₀ S hdrop
  exact ⟨z, hz⟩

/-- The former uniform rank-drop premise implies the selected version used
by the cycle-level first residual. -/
theorem exists_degreeTenComplementCycle_of_regularCubicSectionEmbeddingData_of_finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ S.completion) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  exact exists_degreeTenComplementCycle_of_regularCubicSectionEmbeddingData_of_selectedFinrankDrop
    p hp hne D₁₀ S
    (DegreeTenRegularCubicSectionSelectedFinrankDrop.ofCompletionFinrankDrop
      p hp D₁₀ S hdrop)

end PfaffianDescent
