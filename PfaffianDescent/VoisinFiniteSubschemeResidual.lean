import PfaffianDescent.VoisinFiniteSubschemeSections
import PfaffianDescent.VoisinCompleteIntersectionResidual
import PfaffianDescent.FiniteSubschemeCompleteIntersection
import PfaffianDescent.FiniteClosedSubschemeCycleComplement

/-!
# Residual lengths for actual Voisin subschemes

The section certificates for a finite subscheme of a cubic surface can be
fed directly into the complete-intersection residual calculation.  The
coordinate normalization identifies the original finite scheme with the
corresponding affine chart, so the rank hypothesis transfers without an
extra abstract embedding assumption.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

section
variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra

/- A residual closed subscheme of a finite triple complete intersection
produces an effective zero-cycle of the same degree on the first cubic. -/
omit [Infinite K] in
theorem residual_effectiveZeroCycle_on_cubic_of_rank
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous a) (hg : g.IsHomogeneous b) (hh : h.IsHomogeneous c)
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (n : ℕ)
    (hres : AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = n) :
    ∃ r : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) r = n := by
  obtain ⟨r, hr⟩ := AllCharacteristics.exists_effectiveZeroCycle_of_finite_closed_subscheme
    (finiteClosedResidualι i
      (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)))
    (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
  exact exists_effectiveZeroCycle_on_hypersurface_of_triple f g h hf hg hh n r (hr.trans hres)

/-- A length-sixteen subscheme of a cubic surface, together with two cubic
sections forming the regular Voisin complete intersection, has residual
length eleven whenever that complete intersection is finite étale. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_etale
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      r * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (hqvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hrvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx
        (hqvan x hxgen) (hrvan x hxgen)
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 16 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact triple_cubic_residual_rank_eleven_of_etale
    p q r hp hq hr hne hq0 hrel hregular j hZ

/-- The first residual rank calculation uses only the Frobenius structure of
the finite three-cubic intersection.  Finite étaleness is therefore not part
of the algebraic residual step itself. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_frobenius
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      r * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (hqvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hrvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx
        (hqvan x hxgen) (hrvan x hxgen)
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 16 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact triple_cubic_residual_rank_eleven
    p q r hp hq hr hne hq0 hrel hregular j hZ hfrob

/-- A reduced length-sixteen complete intersection in characteristic zero also
supplies the Frobenius datum needed by the same residual calculation. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_reduced
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      r * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (hqvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hrvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    [IsReduced Γ(scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤)] :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx
        (hqvan x hxgen) (hrvan x hxgen)
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 16 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact triple_cubic_residual_rank_eleven_of_reduced
    p q r hp hq hr hne hq0 hrel hregular j hZ

/- Once explicit cubics have been selected, the remaining residual step is
   exactly the finite-subscheme theorem above; the étaleness premise is kept
   explicit to expose the transversality input. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      r * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hqvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hrvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  exact cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_etale
    p hp hne i hi q r hq hr hq0 hrel hregular hqvan hrvan

/-- The first residual calculation likewise needs selected auxiliary cubics
only on one normalized coordinate system of the length-sixteen subscheme. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (coordinates : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩ := coordinates
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx hqvan hrvan
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 16 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact triple_cubic_residual_rank_eleven_of_etale
    p q r hp hq hr hne hq0 hrel hregular j hZ


/-- A selected normalized coordinate presentation of a rank-sixteen datum
can be used in the first residual calculation under the Frobenius condition. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (coordinates : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩ := coordinates
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx hqvan hrvan
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 16 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact triple_cubic_residual_rank_eleven
    p q r hp hq hr hne hq0 hrel hregular j hZ hfrob

/-- A length-eight subscheme of a cubic surface, together with two quadratic
sections forming the regular Voisin complete intersection, has residual
length four whenever that complete intersection is finite étale. -/
theorem cubicFiniteSubscheme_degree_eight_residual_rank_four_of_etale
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      r * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (hqvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hrvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 4 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx
        (hqvan x hxgen) (hrvan x hxgen)
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 8 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact cubic_two_quadrics_residual_rank_four_of_etale
    p q r hp hq hr hne hq0 hrel hregular j hZ

/-- The final residual rank calculation uses only a Frobenius functional on
the cubic--quadric--quadric intersection. -/
theorem cubicFiniteSubscheme_degree_eight_residual_rank_four_of_frobenius
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      r * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (hqvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hrvan : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ x : Fin 4 → Γ(Z, ⊤),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 4 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx
        (hqvan x hxgen) (hrvan x hxgen)
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 8 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact cubic_two_quadrics_residual_rank_four
    p q r hp hq hr hne hq0 hrel hregular j hZ hfrob

/-- The degree-eight residual calculation only needs the selected quadrics to
vanish for one normalized coordinate system of the finite subscheme.  This is
the form that directly consumes the section-selection theorems, rather than
requiring vanishing for every possible coordinate presentation. -/
theorem cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (coordinates : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 4 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩ := coordinates
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx hqvan hrvan
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 8 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact cubic_two_quadrics_residual_rank_four_of_etale
    p q r hp hq hr hne hq0 hrel hregular j hZ

/-- A normalized rank-eight subscheme contained in a finite
cubic--quadric--quadric intersection directly gives an effective degree-four
cycle on the cubic.  The cycle is the difference of fundamental cycles, so
this conclusion needs neither reducedness nor a Frobenius functional on the
complete intersection. -/
theorem cubicFiniteSubscheme_degree_eight_complement_cycle_degree_four_of_selected_coordinates
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (coordinates : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0) :
    ∃ z : AllCharacteristics.EffectiveZeroCycle (hypersurface p hp),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
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
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase I) = 8 := by
    simpa only [hjbase] using hi
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  have hW : AllCharacteristics.finiteSchemeRank (c ≫ f) = 12 := by
    simpa only [c, f, I, tripleCompleteIntersectionToHypersurface_toBase] using
      cubic_two_quadrics_intersection_length_twelve
        p q r hp hq hr hne hq0 hrel hregular
  have hZ' : AllCharacteristics.finiteSchemeRank (j ≫ c ≫ f) = 8 := by
    simpa only [c, f, I, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hZ
  exact exists_effectiveCycle_of_finite_closed_subscheme_rank_difference
    j c f 12 8 hW hZ'

/-- A selected normalized coordinate presentation of a rank-eight datum can
be used in the final residual calculation under the Frobenius condition. -/
theorem cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_coordinates_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (coordinates : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ j : Z ⟶ scheme
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (finiteClosedResidualι j
            (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
          toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 4 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩ := coordinates
  obtain ⟨j₀, hj₀, hj₀base⟩ :=
    closed_point_of_triple_complete_intersection_coordinates
      p q r hp hq hr x ell hell hxell hxgen hpx hqvan hrvan
  let j : Z ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
    Z.isoSpec.hom ≫ j₀
  haveI : IsClosedImmersion j := by
    dsimp [j]
    infer_instance
  have hjbase : j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      i ≫ hypersurfaceToBase p hp := by
    dsimp [j]
    rw [Category.assoc, hj₀base]
    rw [finiteSchemeCoefficient_spec (i ≫ hypersurfaceToBase p hp)]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]
  haveI : IsFinite (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [hjbase]
    infer_instance
  letI := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  have hZ : AllCharacteristics.finiteSchemeRank (j ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 8 := by
    simpa only [hjbase] using hi
  refine ⟨j, inferInstance, ?_⟩
  exact cubic_two_quadrics_residual_rank_four
    p q r hp hq hr hne hq0 hrel hregular j hZ hfrob

/-- The final `8 → 4` residual step can be made from a length-eight
subscheme on a prime cubic using one normalized coordinate system.  Its only
geometric inputs are a prime cubic--quadric intermediate curve and
transversality of the selected triple intersection; all section counts and
regular-sequence deductions are supplied here. -/
theorem cubicFiniteSubscheme_degree_eight_residual_rank_four_of_prime_cubic_prime_first
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpprime : Prime p)
    (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (hprime : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        ∃ q : MvPolynomial (Fin 4) K,
          q ∈ homogeneousVanishingPolynomialSubmodule (K := K) x 2 ∧ q ≠ 0 ∧
          (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
      (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
      (hregular : ∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
      ∃ j : Z ⟶ scheme
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
        IsClosedImmersion j ∧
        letI := cubic_two_quadrics_intersection_finite p q r hp hq hr hne hq0 hrel hregular
        AllCharacteristics.finiteSchemeRank
          (finiteClosedResidualι j
              (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
            toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 4 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  have hsections : 2 ≤ finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K) x 2)) := by
    apply quadric_degree_eight_vanishing_sections_finrank x
    exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi
  obtain ⟨q, r, hqhom, hrhom, hqvan, hrvan, hq0, hqrel, hregular⟩ :=
    exists_regular_quadric_pair_data_of_prime_cubic_prime_first p hp hpprime x hsections
      (hprime x hxgen)
  letI : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hqhom hrhom)) :=
    htransverse q r hqhom hrhom hq0 hqrel hregular
  obtain ⟨j, hj, hjrank⟩ :=
    cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_coordinates
      p q r hp hqhom hrhom hne hq0 hqrel hregular i hi
      ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩
  exact ⟨q, r, hqhom, hrhom, hq0, hqrel, hregular, j, hj, hjrank⟩

/-- The prime-cubic `8 → 4` construction produces an effective degree-four
zero-cycle on the cubic itself.  The only remaining geometric inputs are the
prime intermediate curve and transversality of the selected intersection. -/
theorem cubicFiniteSubscheme_degree_eight_residual_cycle_degree_four_on_cubic_of_prime_cubic_prime_first
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpprime : Prime p)
    (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (hprime : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
        ∃ q : MvPolynomial (Fin 4) K,
          q ∈ homogeneousVanishingPolynomialSubmodule (K := K) x 2 ∧ q ≠ 0 ∧
          (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ r : AllCharacteristics.EffectiveZeroCycle (hypersurface p hp),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase p hp) r = 4 := by
  obtain ⟨q, r, hq, hr, hq0, hrel, hregular, j, hj, hjrank⟩ :=
    cubicFiniteSubscheme_degree_eight_residual_rank_four_of_prime_cubic_prime_first
      p hp hpprime hne i hi hprime htransverse
  letI : IsClosedImmersion j := hj
  letI := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  exact residual_effectiveZeroCycle_on_cubic_of_rank p q r hp hq hr j 4 hjrank

/-- A selected prime cubic--quadric ideal is enough for the final `8 → 4`
residual.  The second quadric is selected from the proved two-dimensional
vanishing system; no primality assumption on the surface equation is used. -/
theorem cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 8)
    (hselected : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
      (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
      (hregular : ∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
      ∃ j : Z ⟶ scheme
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
        IsClosedImmersion j ∧
        letI := cubic_two_quadrics_intersection_finite p q r hp hq hr hne hq0 hrel hregular
        AllCharacteristics.finiteSchemeRank
          (finiteClosedResidualι j
              (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
            toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 4 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, q, hxgen, hell, hxell, hpx, hqhom, hqvan, hq0, hqrel, hqprime⟩ := hselected
  have hsections : 2 ≤ finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K) x 2)) := by
    apply quadric_degree_eight_vanishing_sections_finrank x
    exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi
  obtain ⟨r, hrhom, hrvan, hregular⟩ :=
    exists_regular_second_quadric_data_of_selected_prime_intermediate
      p q x hp hqhom hsections hqvan hq0 hqprime
  letI : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hqhom hrhom)) :=
    htransverse q r hqhom hrhom hq0 hqrel hregular
  obtain ⟨j, hj, hjrank⟩ :=
    cubicFiniteSubscheme_degree_eight_residual_rank_four_of_selected_coordinates
      p q r hp hqhom hrhom hne hq0 hqrel hregular i hi
      ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩
  exact ⟨q, r, hqhom, hrhom, hq0, hqrel, hregular, j, hj, hjrank⟩

/-- The first `16 → 11` residual step can use the associated-prime
rank-drop conditions directly.  In particular, it does not require the
intermediate ideal generated by the first two cubics to be prime: the third
cubic is selected to be regular modulo that ideal. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hdrop₂ :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3
      let q : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) :=
        (Ideal.Quotient.mkₐ K (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))).toLinearMap
      let V : Submodule K
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) := W.map q
      ∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V)
    (hdrop₃ :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      ∀ (q : MvPolynomial (Fin 4) K),
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3
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
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
      (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
      (hregular : ∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
      ∃ j : Z ⟶ scheme
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
        IsClosedImmersion j ∧
        letI := triple_cubic_intersection_finite p q r hp hq hr hne hq0 hrel hregular
        AllCharacteristics.finiteSchemeRank
          (finiteClosedResidualι j
              (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
            toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
    apply cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
    exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi
  obtain ⟨q, hqhom, hqvan, hq0, hqrel⟩ :=
    exists_regular_cubic_section_data_of_finrank_drop p hp hne x hpx
      (hdrop₂ x hxgen)
  obtain ⟨r, hrhom, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop p q x
      (hdrop₃ x hxgen q)
  letI : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hqhom hrhom)) :=
    htransverse q r hqhom hrhom hq0 hqrel hregular
  obtain ⟨j, hj, hjrank⟩ :=
    cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates
      p q r hp hqhom hrhom hne hq0 hqrel hregular i hi
      ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩
  exact ⟨q, r, hqhom, hrhom, hq0, hqrel, hregular, j, hj, hjrank⟩

/-- For a prime cubic surface, the only remaining section-selection input for
the first residual is the associated-prime rank drop after the first cubic is
chosen.  This replaces the selected-prime-intermediate assumption by the
base-locus condition that Voisin proves geometrically. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_prime_surface_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hdrop₃ :
      letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(Z, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) →
      ∀ (q : MvPolynomial (Fin 4) K),
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(Z, ⊤)) (sigma := Fin 4) x 3
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
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
      (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
      (hregular : ∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
      ∃ j : Z ⟶ scheme
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
        IsClosedImmersion j ∧
        letI := triple_cubic_intersection_finite p q r hp hq hr hne hq0 hrel hregular
        AllCharacteristics.finiteSchemeRank
          (finiteClosedResidualι j
              (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
            toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
    apply cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
    exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi
  obtain ⟨q, hqhom, hqvan, hqnot, hqrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_not_mem p hp hne x hpx hsections hprime
  have hq0 : q ≠ 0 := by
    intro hqzero
    apply hqnot
    rw [hqzero]
    exact Ideal.zero_mem _
  obtain ⟨r, hrhom, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop p q x
      (hdrop₃ x hxgen q)
  letI : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hqhom hrhom)) :=
    htransverse q r hqhom hrhom hq0 hqrel hregular
  obtain ⟨j, hj, hjrank⟩ :=
    cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates
      p q r hp hqhom hrhom hne hq0 hqrel hregular i hi
      ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩
  exact ⟨q, r, hqhom, hrhom, hq0, hqrel, hregular, j, hj, hjrank⟩

/-- The first `16 → 11` residual step admits the same end-to-end packaging.
Starting from a length-sixteen subscheme, prime surface and intermediate
three-cubic intersections select the auxiliary cubics and reduce the residual
calculation to transversality of their complete intersection. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hprime₁ : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hprime₂ : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 3 →
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
      (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
      (hregular : ∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
      ∃ j : Z ⟶ scheme
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
        IsClosedImmersion j ∧
        letI := triple_cubic_intersection_finite p q r hp hq hr hne hq0 hrel hregular
        AllCharacteristics.finiteSchemeRank
          (finiteClosedResidualι j
              (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
            toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxgen, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp i
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
    apply cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
    exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi
  obtain ⟨q, hqhom, hqvan, hqnot, hqrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_not_mem p hp hne x hpx hsections hprime₁
  have hq0 : q ≠ 0 := by
    intro hqzero
    apply hqnot
    rw [hqzero]
    exact Ideal.zero_mem _
  obtain ⟨r, hrhom, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_prime_and_sections
      p q x (hprime₂ q hqhom) hp hpx hqhom hqvan hsections
  letI : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hqhom hrhom)) :=
    htransverse q r hqhom hrhom hq0 hqrel hregular
  obtain ⟨j, hj, hjrank⟩ :=
    cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates
      p q r hp hqhom hrhom hne hq0 hqrel hregular i hi
      ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩
  exact ⟨q, r, hqhom, hrhom, hq0, hqrel, hregular, j, hj, hjrank⟩

/-- The prime-intermediate `16 → 11` construction produces an effective
degree-eleven zero-cycle on the cubic itself.  The outstanding inputs are the
primality and transversality assertions made explicit below. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_cycle_degree_eleven_on_cubic_of_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hprime₁ : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hprime₂ : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 3 →
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ r : AllCharacteristics.EffectiveZeroCycle (hypersurface p hp),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase p hp) r = 11 := by
  obtain ⟨q, r, hq, hr, hq0, hrel, hregular, j, hj, hjrank⟩ :=
    cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_prime_intermediate
      p hp hne i hi hprime₁ hprime₂ htransverse
  letI : IsClosedImmersion j := hj
  letI := triple_cubic_intersection_finite p q r hp hq hr hne hq0 hrel hregular
  exact residual_effectiveZeroCycle_on_cubic_of_rank p q r hp hq hr j 11 hjrank

/-- A selected prime cubic through a length-sixteen datum is sufficient for
Voisin's first complete-intersection residual.  The proof chooses the third
cubic from the section-count argument, so it needs primeness only for the
selected intermediate ideal, rather than for every auxiliary cubic. -/
theorem cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase p hp) = 16)
    (hselected : letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(Z, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
      (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
      (hregular : ∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
      ∃ j : Z ⟶ scheme
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
        IsClosedImmersion j ∧
        letI := triple_cubic_intersection_finite p q r hp hq hr hne hq0 hrel hregular
        AllCharacteristics.finiteSchemeRank
          (finiteClosedResidualι j
              (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ≫
            toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 11 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (i ≫ hypersurfaceToBase p hp)
  haveI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, q, hxgen, hell, hxell, hpx, hqhom, hqvan, hq0, hqrel, hqprime⟩ := hselected
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx := by
    apply cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
    exact (finiteSchemeCoefficient_finrank (i ≫ hypersurfaceToBase p hp)).trans hi
  obtain ⟨r, hrhom, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_prime_and_sections
      p q x hqprime hp hpx hqhom hqvan hsections
  letI : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hqhom hrhom)) :=
    htransverse q r hqhom hrhom hq0 hqrel hregular
  obtain ⟨j, hj, hjrank⟩ :=
    cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_selected_coordinates
      p q r hp hqhom hrhom hne hq0 hqrel hregular i hi
      ⟨x, ell, hxgen, hell, hxell, hpx, hqvan, hrvan⟩
  exact ⟨q, r, hqhom, hrhom, hq0, hqrel, hregular, j, hj, hjrank
    ⟩

end
end PfaffianDescent
