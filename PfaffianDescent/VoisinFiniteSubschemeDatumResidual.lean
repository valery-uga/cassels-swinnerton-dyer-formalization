import AllCharacteristics.FiniteSubschemeRank
import PfaffianDescent.FiniteSubschemeResidualDatum
import PfaffianDescent.VoisinFiniteSubschemeResidual
import PfaffianDescent.NormalizedTripleCompleteIntersection

/-!
# Voisin residuals from finite-subscheme data

The universal finite-subscheme interface retains an ideal-defined closed
subscheme of fixed rank.  This file feeds that datum directly to the first
complete-intersection residual calculation in Voisin's degree-ten argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Transport a complete-intersection embedding from any scheme presentation
of a finite-subscheme datum to the datum's canonical ideal-defined
subscheme.  Geometric constructions frequently work with a chosen finite
scheme before it is converted to `FiniteSubschemeDatum`; this definition
keeps the resulting containment in the complete intersection rather than
discarding it when that conversion introduces an isomorphic source. -/
noncomputable def finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso
    (p q r : MvPolynomial (Fin 4) K)
    {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    {Z : Scheme.{u}} (e : Z ≅ D.val.subscheme)
    (j : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) :
    D.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
  e.inv ≫ j

/-- The transported complete-intersection map is still a closed immersion. -/
instance finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso_isClosedImmersion
    (p q r : MvPolynomial (Fin 4) K)
    {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    {Z : Scheme.{u}} (e : Z ≅ D.val.subscheme)
    (j : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j] :
    IsClosedImmersion
      (finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso p q r hp hq hr n D e j) := by
  dsimp [finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso]
  infer_instance

/-- If an embedding of an isomorphic presentation is over the original
cubic, its transport is over the canonical finite-subscheme immersion. -/
theorem finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso_fac
    (p q r : MvPolynomial (Fin 4) K)
    {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    {Z : Scheme.{u}} (e : Z ≅ D.val.subscheme)
    (j : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      e.hom ≫ D.val.subschemeι) :
    finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso p q r hp hq hr n D e j ≫
        tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      D.val.subschemeι := by
  dsimp [finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso]
  rw [Category.assoc, hj, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- A normalized projective chart for a finite-subscheme datum, together with
vanishing of two selected cubics, gives an actual immersion of that datum into
their three-cubic complete intersection.  The construction retains equality
over the original cubic surface, which is stronger than equality after
composition to the ground field. -/
noncomputable def finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) {b c : ℕ}
    (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    (chart : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
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
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
          D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι) :
    D.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) := by
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  let z := Classical.choose chart
  let chart₁ := Classical.choose_spec chart
  let hz := Classical.choose chart₁
  let chart₂ := Classical.choose_spec chart₁
  let x := Classical.choose chart₂
  let chart₃ := Classical.choose_spec chart₂
  let he := Classical.choose chart₃
  let chart₄ := Classical.choose_spec chart₃
  let hzOne := Classical.choose chart₄
  let chart₅ := Classical.choose_spec chart₄
  let hgen := chart₅.1
  let hqx := chart₅.2.1
  let hrx := chart₅.2.2.1
  let hpoint := chart₅.2.2.2
  have hpIdeal : p ∈ (equationIdeal p hp).toIdeal :=
    Ideal.subset_span (by simp)
  have hpx : p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 := by
    change (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) p = 0
    exact he p hpIdeal
  exact Classical.choose
    (normalizedPointAt_tripleCompleteIntersectionEmbedding_of_isoSpec
      p q r hp hq hr D.val.subschemeι x hpx hqx hrx z hz he hzOne hgen hpoint)

/-- The normalized-chart immersion is a closed immersion. -/
theorem finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart_isClosedImmersion
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) {b c : ℕ}
    (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    (chart : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
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
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
          D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι) :
    IsClosedImmersion
      (finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart
        p q r hp hq hr n D chart) := by
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  let z := Classical.choose chart
  let chart₁ := Classical.choose_spec chart
  let hz := Classical.choose chart₁
  let chart₂ := Classical.choose_spec chart₁
  let x := Classical.choose chart₂
  let chart₃ := Classical.choose_spec chart₂
  let he := Classical.choose chart₃
  let chart₄ := Classical.choose_spec chart₃
  let hzOne := Classical.choose chart₄
  let chart₅ := Classical.choose_spec chart₄
  let hgen := chart₅.1
  let hqx := chart₅.2.1
  let hrx := chart₅.2.2.1
  let hpoint := chart₅.2.2.2
  have hpIdeal : p ∈ (equationIdeal p hp).toIdeal :=
    Ideal.subset_span (by simp)
  have hpx : p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 := by
    change (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) p = 0
    exact he p hpIdeal
  let embeddingExists :=
    normalizedPointAt_tripleCompleteIntersectionEmbedding_of_isoSpec
      p q r hp hq hr D.val.subschemeι x hpx hqx hrx z hz he hzOne hgen hpoint
  change IsClosedImmersion (Classical.choose embeddingExists)
  exact (Classical.choose_spec embeddingExists).1

/-- The normalized-chart immersion recovers the original finite-subscheme
map to the cubic surface. -/
theorem finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart_fac
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) {b c : ℕ}
    (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    (chart : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
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
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
          D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι) :
    finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart
      p q r hp hq hr n D chart ≫
        tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      D.val.subschemeι := by
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  let z := Classical.choose chart
  let chart₁ := Classical.choose_spec chart
  let hz := Classical.choose chart₁
  let chart₂ := Classical.choose_spec chart₁
  let x := Classical.choose chart₂
  let chart₃ := Classical.choose_spec chart₂
  let he := Classical.choose chart₃
  let chart₄ := Classical.choose_spec chart₃
  let hzOne := Classical.choose chart₄
  let chart₅ := Classical.choose_spec chart₄
  let hgen := chart₅.1
  let hqx := chart₅.2.1
  let hrx := chart₅.2.2.1
  let hpoint := chart₅.2.2.2
  have hpIdeal : p ∈ (equationIdeal p hp).toIdeal :=
    Ideal.subset_span (by simp)
  have hpx : p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 := by
    change (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) p = 0
    exact he p hpIdeal
  let embeddingExists :=
    normalizedPointAt_tripleCompleteIntersectionEmbedding_of_isoSpec
      p q r hp hq hr D.val.subschemeι x hpx hqx hrx z hz he hzOne hgen hpoint
  change Classical.choose embeddingExists ≫
      tripleCompleteIntersectionToHypersurface p q r hp hq hr =
    D.val.subschemeι
  exact (Classical.choose_spec embeddingExists).2

/-- A rank-sixteen finite-subscheme datum on a cubic surface can be used
directly in the first cubic residual calculation.  The only remaining
geometric premises are the chosen vanishing cubics and étaleness of their
complete intersection. -/
theorem finiteSubschemeDatum_degree_sixteen_residual_rank_eleven_of_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ j : D.val.subscheme ⟶
        scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  let i : D.val.subscheme ⟶ hypersurface p hp := D.val.subschemeι
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ hypersurfaceToBase p hp) := by
    change IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    exact D.property.1
  have hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16 := by
    rw [finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint K)
  exact cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular i hi coordinates

/-- A transverse three-cubic residual to a rank-sixteen datum is itself an
ideal-defined finite-flat datum of rank eleven on the original cubic.  This
keeps the residual scheme available for the subsequent rank-two step, rather
than retaining only its fundamental cycle. -/
noncomputable def finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 11 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  let j := Classical.choose
    (finiteSubschemeDatum_degree_sixteen_residual_rank_eleven_of_selected_coordinates
      p q r hp hq hr hne hq0 hrel hregular D coordinates)
  have hj : IsClosedImmersion j :=
    (Classical.choose_spec
      (finiteSubschemeDatum_degree_sixteen_residual_rank_eleven_of_selected_coordinates
        p q r hp hq hr hne hq0 hrel hregular D coordinates)).1
  have hjres : finiteSchemeRank
      (finiteClosedResidualι j (toBase I) ≫ toBase I) = 11 :=
    (Classical.choose_spec
      (finiteSubschemeDatum_degree_sixteen_residual_rank_eleven_of_selected_coordinates
        p q r hp hq hr hne hq0 hrel hregular D coordinates)).2
  letI : IsClosedImmersion j := hj
  letI : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 27 :=
    triple_cubic_intersection_length_twenty_seven
      p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 27 d hI rfl
      (finiteEtaleScheme_exists_frobeniusFunctional (toBase I))
    rw [hjres] at hcomp
    change d = 16
    omega
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))

/-- The selected-coordinate first residual produces a finite-flat rank-eleven
datum from the Frobenius property of its complete intersection. -/
noncomputable def finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 11 := by
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
  let j := Classical.choose
    (cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates_of_frobenius
      p q r hp hq hr hne hq0 hrel hregular D.val.subschemeι
      (by
        rw [finiteSchemeRank_eq_finrank]
        exact D.property.2.2.2 (IsLocalRing.closedPoint K)) coordinates hfrob)
  have hj : IsClosedImmersion j :=
    (Classical.choose_spec
      (cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates_of_frobenius
        p q r hp hq hr hne hq0 hrel hregular D.val.subschemeι
        (by
          rw [finiteSchemeRank_eq_finrank]
          exact D.property.2.2.2 (IsLocalRing.closedPoint K)) coordinates hfrob)).1
  have hjres : finiteSchemeRank
      (finiteClosedResidualι j (toBase I) ≫ toBase I) = 11 :=
    (Classical.choose_spec
      (cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates_of_frobenius
        p q r hp hq hr hne hq0 hrel hregular D.val.subschemeι
        (by
          rw [finiteSchemeRank_eq_finrank]
          exact D.property.2.2.2 (IsLocalRing.closedPoint K)) coordinates hfrob)).2
  letI : IsClosedImmersion j := hj
  letI : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 27 :=
    triple_cubic_intersection_length_twenty_seven
      p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 27 d hI rfl hfrob
    rw [hjres] at hcomp
    change d = 16
    omega
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  apply finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
  apply finiteScheme_exists_frobeniusFunctional_congr (toBase I) (c ≫ f)
  · exact (tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr).symm
  · exact hfrob

/-- The rank-eleven datum constructed from selected coordinates is finite
étale over the base field.  This exposes the geometric output of a single
transverse three-cubic triple without requiring a separate embedding witness. -/
theorem finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates_toBase_etale
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    Etale ((finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates
      p q r hp hq hr hne hq0 hrel hregular D coordinates).val.subschemeι ≫
        hypersurfaceToBase p hp) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  let _ : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  let _ : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  let _ : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  let j := Classical.choose
    (finiteSubschemeDatum_degree_sixteen_residual_rank_eleven_of_selected_coordinates
      p q r hp hq hr hne hq0 hrel hregular D coordinates)
  have hj : IsClosedImmersion j :=
    (Classical.choose_spec
      (finiteSubschemeDatum_degree_sixteen_residual_rank_eleven_of_selected_coordinates
        p q r hp hq hr hne hq0 hrel hregular D coordinates)).1
  have hjres : finiteSchemeRank
      (finiteClosedResidualι j (toBase I) ≫ toBase I) = 11 :=
    (Classical.choose_spec
      (finiteSubschemeDatum_degree_sixteen_residual_rank_eleven_of_selected_coordinates
        p q r hp hq hr hne hq0 hrel hregular D coordinates)).2
  let _ : IsClosedImmersion j := hj
  let _ : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 27 :=
    triple_cubic_intersection_length_twenty_seven
      p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 27 d hI rfl
      (finiteEtaleScheme_exists_frobeniusFunctional (toBase I))
    rw [hjres] at hcomp
    change d = 16
    omega
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  change Etale ((finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))).val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    j c f 27 16 hX hZ

/-- Associated-component avoidance for one chosen cubic--cubic intersection
selects the third cubic through a rank-sixteen datum.  Together with
transversality for that selected triple it yields the finite étale rank-eleven
residual.  This is the datum-level form of the geometric conclusion of
Voisin's Lemma 3.3, with no primeness hypothesis on the intermediate curve. -/
theorem exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_avoids_associatedPrimes
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hne : p ≠ 0)
    (hrel : IsRelPrime p q)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        (∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
          ∃ r ∈ homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3,
            Ideal.Quotient.mk (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) r ∉ P))
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K)
      (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, havoid⟩ := coordinates
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_avoids_associatedPrimes p q x havoid
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) :=
    htransverse r hr hregular
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩

/-- An actual embedding of the rank-sixteen datum into the selected
three-cubic intersection supplies the first residual datum without a separate
choice of normalized coordinates.  The embedding records precisely that the
chosen cubics contain the original datum. -/
noncomputable def finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    [CharZero K]
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
      D.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 11 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hjbase : j ≫ toBase I = D.val.subschemeι ≫ f := by
    calc
      j ≫ toBase I = j ≫ (c ≫ f) := by
        rw [tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
      _ = (j ≫ c) ≫ f := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ f := by rw [hj]
  letI : IsFinite (j ≫ toBase I) := by
    rw [hjbase]
    exact D.property.1
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using
      triple_cubic_intersection_length_twenty_seven
        p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))

/-- The first residual construction only needs a Frobenius functional on the
three-cubic intersection to produce its finite-flat rank-eleven datum.
Étaleness is a later, stronger condition used when that datum must itself be
finite étale. -/
noncomputable def finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_of_frobenius
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
      D.val.subschemeι)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 11 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hjbase : j ≫ toBase I = D.val.subschemeι ≫ f := by
    calc
      j ≫ toBase I = j ≫ (c ≫ f) := by
        rw [tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
      _ = (j ≫ c) ≫ f := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ f := by rw [hj]
  letI : IsFinite (j ≫ toBase I) := by
    rw [hjbase]
    exact D.property.1
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using
      triple_cubic_intersection_length_twenty_seven
        p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  apply finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
  apply finiteScheme_exists_frobeniusFunctional_congr (toBase I) (c ≫ f)
  · exact (tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr).symm
  · exact hfrob

/-- The rank-eleven datum obtained as the residual to a rank-sixteen datum in
a transverse three-cubic intersection is finite étale over the base field.
This is the datum-level form of the first `16 → 11` step, needed when the
rank-two construction takes the residual scheme itself as its ambient input. -/
theorem finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_toBase_etale
    [CharZero K]
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
      D.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    Etale
      ((finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
        p q r hp hq hr hne hq0 hrel hregular D j hj).val.subschemeι ≫
          hypersurfaceToBase p hp) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hjbase : j ≫ toBase I = D.val.subschemeι ≫ f := by
    calc
      j ≫ toBase I = j ≫ (c ≫ f) := by
        rw [tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
      _ = (j ≫ c) ≫ f := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ f := by rw [hj]
  letI : IsFinite (j ≫ toBase I) := by
    rw [hjbase]
    exact D.property.1
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using
      triple_cubic_intersection_length_twenty_seven
        p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  change Etale ((finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))).val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    j c f 27 16 hX hZ

/-- In the transverse three-cubic construction, the rank-eleven residual is
disjoint from the embedded rank-sixteen datum.  Thus the first Voisin pencil
does not require this support condition as an additional geometric input. -/
theorem disjoint_finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    [CharZero K]
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
      D.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
        (finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
          p q r hp hq hr hne hq0 hrel hregular D j hj)))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D)) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hjbase : j ≫ toBase I = D.val.subschemeι ≫ f := by
    calc
      j ≫ toBase I = j ≫ (c ≫ f) := by
        rw [tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
      _ = (j ≫ c) ≫ f := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ f := by rw [hj]
  letI : IsFinite (j ≫ toBase I) := by
    rw [hjbase]
    exact D.property.1
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using
      triple_cubic_intersection_length_twenty_seven
        p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  change Disjoint
    (Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
        (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f)))))
    (Set.range (finiteSubschemeDatumSpecMap f D))
  exact disjoint_finiteSubschemeDatumOfFiniteResidualOnAmbient_of_finiteEtale
    c f 27 16 hX D j hj hZ

/-- A rank-eight finite-subscheme datum on a cubic surface can likewise be
fed directly to the final cubic--two-quadric residual calculation. -/
theorem finiteSubschemeDatum_degree_eight_residual_rank_four_of_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ j : D.val.subscheme ⟶
        scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 4 := by
  let i : D.val.subscheme ⟶ hypersurface p hp := D.val.subschemeι
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ hypersurfaceToBase p hp) := by
    change IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    exact D.property.1
  have hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8 := by
    rw [finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint K)
  exact cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular i hi coordinates

/-- A transverse cubic--quadric--quadric residual to a rank-eight datum is
an ideal-defined finite-flat datum of rank four on the original cubic. -/
noncomputable def finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  let j := Classical.choose
    (finiteSubschemeDatum_degree_eight_residual_rank_four_of_selected_coordinates
      p q r hp hq hr hne hq0 hrel hregular D coordinates)
  have hj : IsClosedImmersion j :=
    (Classical.choose_spec
      (finiteSubschemeDatum_degree_eight_residual_rank_four_of_selected_coordinates
        p q r hp hq hr hne hq0 hrel hregular D coordinates)).1
  have hjres : finiteSchemeRank
      (finiteClosedResidualι j (toBase I) ≫ toBase I) = 4 :=
    (Classical.choose_spec
      (finiteSubschemeDatum_degree_eight_residual_rank_four_of_selected_coordinates
        p q r hp hq hr hne hq0 hrel hregular D coordinates)).2
  letI : IsClosedImmersion j := hj
  letI : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 12 :=
    cubic_two_quadrics_intersection_length_twelve
      p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 8 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 12 d hI rfl
      (finiteEtaleScheme_exists_frobeniusFunctional (toBase I))
    rw [hjres] at hcomp
    change d = 8
    omega
  have hX : finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 12 8 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))

/-- The selected-coordinate final residual produces a finite-flat rank-four
datum from the Frobenius property of its complete intersection. -/
noncomputable def finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  let j := Classical.choose
    (cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_coordinates_of_frobenius
      p q r hp hq hr hne hq0 hrel hregular D.val.subschemeι
      (by
        rw [finiteSchemeRank_eq_finrank]
        exact D.property.2.2.2 (IsLocalRing.closedPoint K)) coordinates hfrob)
  have hj : IsClosedImmersion j :=
    (Classical.choose_spec
      (cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_coordinates_of_frobenius
        p q r hp hq hr hne hq0 hrel hregular D.val.subschemeι
        (by
          rw [finiteSchemeRank_eq_finrank]
          exact D.property.2.2.2 (IsLocalRing.closedPoint K)) coordinates hfrob)).1
  have hjres : finiteSchemeRank
      (finiteClosedResidualι j (toBase I) ≫ toBase I) = 4 :=
    (Classical.choose_spec
      (cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_coordinates_of_frobenius
        p q r hp hq hr hne hq0 hrel hregular D.val.subschemeι
        (by
          rw [finiteSchemeRank_eq_finrank]
          exact D.property.2.2.2 (IsLocalRing.closedPoint K)) coordinates hfrob)).2
  letI : IsClosedImmersion j := hj
  letI : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 12 :=
    cubic_two_quadrics_intersection_length_twelve
      p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 8 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 12 d hI rfl hfrob
    rw [hjres] at hcomp
    change d = 8
    omega
  have hX : finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  apply finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 12 8 hX hZ
  apply finiteScheme_exists_frobeniusFunctional_congr (toBase I) (c ≫ f)
  · exact (tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr).symm
  · exact hfrob

/-- The rank-four datum constructed from selected quadratic coordinates is
finite étale over the base field.  Thus the final transverse residual carries
the same scheme-level regularity as the preceding rank-eleven residual. -/
theorem finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates_toBase_etale
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    Etale ((finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates
      p q r hp hq hr hne hq0 hrel hregular D coordinates).val.subschemeι ≫
        hypersurfaceToBase p hp) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  let _ : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  let _ : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  let _ : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  let j := Classical.choose
    (finiteSubschemeDatum_degree_eight_residual_rank_four_of_selected_coordinates
      p q r hp hq hr hne hq0 hrel hregular D coordinates)
  have hj : IsClosedImmersion j :=
    (Classical.choose_spec
      (finiteSubschemeDatum_degree_eight_residual_rank_four_of_selected_coordinates
        p q r hp hq hr hne hq0 hrel hregular D coordinates)).1
  have hjres : finiteSchemeRank
      (finiteClosedResidualι j (toBase I) ≫ toBase I) = 4 :=
    (Classical.choose_spec
      (finiteSubschemeDatum_degree_eight_residual_rank_four_of_selected_coordinates
        p q r hp hq hr hne hq0 hrel hregular D coordinates)).2
  let _ : IsClosedImmersion j := hj
  let _ : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 12 :=
    cubic_two_quadrics_intersection_length_twelve
      p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 8 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 12 d hI rfl
      (finiteEtaleScheme_exists_frobeniusFunctional (toBase I))
    rw [hjres] at hcomp
    change d = 8
    omega
  have hX : finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  change Etale ((finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 12 8 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))).val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    j c f 12 8 hX hZ

/-- An actual embedding of the rank-eight datum into the selected
cubic--quadric--quadric intersection supplies the final residual datum
without a separate normalized-coordinate choice. -/
noncomputable def finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (j : D.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      D.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hjbase : j ≫ toBase I = D.val.subschemeι ≫ f := by
    calc
      j ≫ toBase I = j ≫ (c ≫ f) := by
        rw [tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
      _ = (j ≫ c) ≫ f := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ f := by rw [hj]
  letI : IsFinite (j ≫ toBase I) := by
    rw [hjbase]
    exact D.property.1
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 8 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  have hX : finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using
      cubic_two_quadrics_intersection_length_twelve
        p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 12 8 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))

/-- The final cubic--quadric--quadric residual likewise needs only a
Frobenius functional to produce its finite-flat rank-four datum. -/
noncomputable def finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (j : D.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      D.val.subschemeι)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hjbase : j ≫ toBase I = D.val.subschemeι ≫ f := by
    calc
      j ≫ toBase I = j ≫ (c ≫ f) := by
        rw [tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
      _ = (j ≫ c) ≫ f := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ f := by rw [hj]
  letI : IsFinite (j ≫ toBase I) := by
    rw [hjbase]
    exact D.property.1
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 8 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  have hX : finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using
      cubic_two_quadrics_intersection_length_twelve
        p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  apply finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 12 8 hX hZ
  apply finiteScheme_exists_frobeniusFunctional_congr (toBase I) (c ≫ f)
  · exact (tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr).symm
  · exact hfrob

/-- The rank-sixteen datum form of the first residual construction produces
an effective degree-eleven cycle on the original cubic surface. -/
theorem finiteSubschemeDatum_degree_sixteen_residual_cycle_degree_eleven_of_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D coordinates
  exact ⟨finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R,
    finiteSubschemeDatumCycle_degree _ _⟩

/-- A rank-eight datum contained in a finite cubic--quadric--quadric
intersection produces an effective degree-four cycle by subtracting
fundamental cycles.  This is the cycle-level form of Voisin's final `8 → 4`
step and requires no reducedness or Frobenius hypothesis. -/
theorem
    finiteSubschemeDatum_degree_eight_complement_cycle_degree_four_of_selected_coordinates
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫
          hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra
        (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
        (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧
        ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  let i : D.val.subscheme ⟶ hypersurface p hp := D.val.subschemeι
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ hypersurfaceToBase p hp) := by
    change IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    exact D.property.1
  have hi : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8 := by
    rw [finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint K)
  exact
    cubicFiniteSubscheme_degree_eight_complement_cycle_degree_four_of_selected_coordinates
      p q r hp hq hr hne hq0 hrel hregular i hi coordinates

/-- The rank-eight datum form of the final residual-scheme construction
produces an effective degree-four cycle on the original cubic surface. -/
theorem finiteSubschemeDatum_degree_eight_residual_cycle_degree_four_of_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  let R := finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D coordinates
  exact ⟨finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R,
    finiteSubschemeDatumCycle_degree _ _⟩

/-- The same degree-four cycle conclusion needs only the Frobenius property
of the finite cubic--quadric--quadric complete intersection.  Reducedness or
étaleness is not part of Voisin's proper-intersection argument; either may be
used later as one way of supplying this algebraic input. -/
theorem
    finiteSubschemeDatum_degree_eight_residual_cycle_degree_four_of_selected_coordinates_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫
          hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra
        (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
        (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom
          (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧
        ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  let R :=
    finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates_of_frobenius
      p q r hp hq hr hne hq0 hrel hregular D coordinates hfrob
  exact ⟨finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R,
    finiteSubschemeDatumCycle_degree _ _⟩

/-- The rank-four datum obtained from an embedded rank-eight datum in a
transverse cubic--quadric--quadric intersection is finite étale over the
base field.  This retains the scheme-level property needed to specialize the
final residual construction. -/
theorem finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding_toBase_etale
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (j : D.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      D.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    Etale
      ((finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
        p q r hp hq hr hne hq0 hrel hregular D j hj).val.subschemeι ≫
          hypersurfaceToBase p hp) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hjbase : j ≫ toBase I = D.val.subschemeι ≫ f := by
    calc
      j ≫ toBase I = j ≫ (c ≫ f) := by
        rw [tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
      _ = (j ≫ c) ≫ f := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ f := by rw [hj]
  letI : IsFinite (j ≫ toBase I) := by
    rw [hjbase]
    exact D.property.1
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 8 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  have hX : finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using
      cubic_two_quadrics_intersection_length_twelve
        p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  change Etale ((finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 12 8 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))).val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    j c f 12 8 hX hZ

/-- In the transverse cubic--quadric--quadric construction, the rank-four
residual is disjoint from the embedded rank-eight datum.  This removes the
final support-separation premise from the residual calculation itself. -/
theorem disjoint_finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (j : D.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      D.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
        (finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
          p q r hp hq hr hne hq0 hrel hregular D j hj)))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D)) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hjbase : j ≫ toBase I = D.val.subschemeι ≫ f := by
    calc
      j ≫ toBase I = j ≫ (c ≫ f) := by
        rw [tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
      _ = (j ≫ c) ≫ f := by rw [Category.assoc]
      _ = D.val.subschemeι ≫ f := by rw [hj]
  letI : IsFinite (j ≫ toBase I) := by
    rw [hjbase]
    exact D.property.1
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 8 := by
    rw [finiteSchemeRank_eq_finrank]
    simpa only [hjbase] using D.property.2.2.2 (IsLocalRing.closedPoint K)
  have hX : finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using
      cubic_two_quadrics_intersection_length_twelve
        p q r hp hq hr hne hq0 hrel hregular
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  change Disjoint
    (Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 12 8 hX hZ
        (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f)))))
    (Set.range (finiteSubschemeDatumSpecMap f D))
  exact disjoint_finiteSubschemeDatumOfFiniteResidualOnAmbient_of_finiteEtale
    c f 12 8 hX D j hj hZ

/-- The selected-prime first residual construction returns an actual finite
étale rank-eleven finite-subscheme datum.  Its third cubic is selected from
the proved section-count bound. -/
theorem exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (hselected : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
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
  obtain ⟨q, r, hq, hr, hq0, hrel, hregular, j, hj, hjres⟩ :=
    cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_prime_intermediate
      p hp hne i hi hselected htransverse
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsClosedImmersion j := hj
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    exact htransverse q r hq hr hq0 hrel hregular
  letI : Etale (toBase I) := htransverse q r hq hr hq0 hrel hregular
  letI : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 27 :=
    triple_cubic_intersection_length_twenty_seven p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 27 d hI rfl
      (finiteEtaleScheme_exists_frobeniusFunctional (toBase I))
    rw [hjres] at hcomp
    change d = 16
    omega
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  let R := finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  dsimp [R]
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    j c f 27 16 hX hZ

/-- Forgetting the étaleness certificate recovers the original selected-prime
rank-eleven residual statement. -/
theorem exists_finiteSubschemeDatum_degree_sixteen_residual_of_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (hselected : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  obtain ⟨R, hR, -⟩ :=
    exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_prime_intermediate
      p hp hne D hselected htransverse
  exact ⟨R, hR⟩

/-- Voisin's base-locus alternative gives the first residual without asking
for the intermediate cubic--cubic curve to be integral.  The surface remains
prime, the first cubic is chosen by prime avoidance, and the displayed
associated-prime rank drop selects the third cubic.  This is the exact
algebraic output of Lemma 3.3 once its geometric avoidance statement is
proved for the moving degree-sixteen datum. -/
theorem exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_prime_surface_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hdrop₃ :
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) →
      ∀ (q : MvPolynomial (Fin 4) K),
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3
      let qmap : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
          (MvPolynomial (Fin 4) K ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
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
  obtain ⟨q, r, hq, hr, hq0, hrel, hregular, j, hj, hjres⟩ :=
    cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_prime_surface_and_finrank_drop
      p hp hne i hi hprime hdrop₃ htransverse
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsClosedImmersion j := hj
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    exact htransverse q r hq hr hq0 hrel hregular
  letI : Etale (toBase I) := htransverse q r hq hr hq0 hrel hregular
  letI : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 27 :=
    triple_cubic_intersection_length_twenty_seven p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 27 d hI rfl
      (finiteEtaleScheme_exists_frobeniusFunctional (toBase I))
    rw [hjres] at hcomp
    change d = 16
    omega
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  let R := finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  dsimp [R]
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    j c f 27 16 hX hZ

/-- Forgetting the étaleness certificate leaves the finite-flat rank-eleven
residual needed by the next numerical step. -/
theorem exists_finiteSubschemeDatum_degree_sixteen_residual_of_prime_surface_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hdrop₃ :
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) →
      ∀ (q : MvPolynomial (Fin 4) K),
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3
      let qmap : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
          (MvPolynomial (Fin 4) K ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  obtain ⟨R, hR, -⟩ :=
    exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_prime_surface_and_finrank_drop
      p hp hne D hprime hdrop₃ htransverse
  exact ⟨R, hR⟩

/-- The selected-prime final residual construction returns an actual finite
étale rank-four finite-subscheme datum.  Its second quadric is selected from
the proved section-count bound. -/
theorem exists_finiteSubschemeDatum_degree_eight_residual_of_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hselected : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let i : D.val.subscheme ⟶ hypersurface p hp := D.val.subschemeι
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ hypersurfaceToBase p hp) := by
    change IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    exact D.property.1
  have hi : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8 := by
    rw [finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint K)
  obtain ⟨q, r, hq, hr, hq0, hrel, hregular, j, hj, hjres⟩ :=
    cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_prime_intermediate
      p hp hne i hi hselected htransverse
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsClosedImmersion j := hj
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    exact htransverse q r hq hr hq0 hrel hregular
  letI : Etale (toBase I) := htransverse q r hq hr hq0 hrel hregular
  letI : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 12 :=
    cubic_two_quadrics_intersection_length_twelve p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 8 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 12 d hI rfl
      (finiteEtaleScheme_exists_frobeniusFunctional (toBase I))
    rw [hjres] at hcomp
    change d = 8
    omega
  have hX : finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  let R := finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 12 8 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  dsimp [R]
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    j c f 12 8 hX hZ

/-- The final `8 → 4` residual can use the exact quotient rank-drop estimate
for one selected cubic--quadric curve.  The estimate selects the second
quadric internally, so no primeness assertion on the intermediate curve is
needed. -/
theorem exists_finiteSubschemeDatum_degree_eight_residual_and_toBase_etale_of_selected_finrank_drop
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (coordinates : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hdrop : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) →
        let W := homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 2
        let qmap : MvPolynomial (Fin 4) K →ₗ[K]
            MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
        let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
        ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
            (MvPolynomial (Fin 4) K ⧸ I),
          Module.finrank K ((P.restrictScalars K).comap V.subtype) <
            Module.finrank K V)
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K)
      (hr : r.IsHomogeneous 2),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan⟩ := coordinates
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_second_quadric_data_of_finrank_drop p q x (hdrop x hxsurj)
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) :=
    htransverse r hr hregular
  let R := finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩

/-- A single regular transverse quadric through the rank-eight datum gives the
final finite étale residual. This is the point-specific Bertini interface: it
does not require transversality for every regular member of the quadratic
system. -/
theorem exists_finiteSubschemeDatum_degree_eight_residual_and_toBase_etale_of_selected_regular_transverse_quadric
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (selected : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell r : MvPolynomial (Fin 4) K)
        (hr : r.IsHomogeneous 2),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
        Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, r, hr, hxsurj, hell, hxell, hpx, hqvan, hrvan, hregular, htransverse⟩ := selected
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := htransverse
  let R := finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩

/-- A single regular transverse third cubic through the rank-sixteen datum
gives the first finite étale residual. This is the point-specific form of the
first Bertini step and does not assert transversality for every regular cubic
in the system. -/
theorem exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_regular_transverse_cubic
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    (selected : letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell r : MvPolynomial (Fin 4) K)
        (hr : r.IsHomogeneous 3),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
        Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, r, hr, hxsurj, hell, hxell, hpx, hqvan, hrvan, hregular, htransverse⟩ := selected
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := htransverse
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩

end PfaffianDescent
