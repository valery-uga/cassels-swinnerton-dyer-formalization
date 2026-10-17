import PfaffianDescent.ProjectiveGeneralPosition

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinates constructed from an actual finite reduced embedded scheme
have both its homogeneous ideal and its geometric general position. -/
theorem reduced_projective_general_position_coordinates
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} [AlgebraicGeometry.IsReduced Z]
    (i : Z ⟶ scheme I) [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    (hp : ProjectiveGeometricGeneralPosition I i) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ p : Fin 4 → Γ(Z, ⊤), AlgebraGeometricGeneralPosition (K := K) p ∧
      (projectiveSubschemeIdeal I i).toIdeal = algebraVectorIdeal (K := K) p := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  obtain ⟨z, hz, g, _, hbase, hg⟩ := finite_projective_closed_subscheme_chart I i
  exact ⟨fun j => g (linearChartCoordinate I z hz j), hp.algebra i z hz g hg,
    projectiveSubschemeIdeal_eq_algebraVectorIdeal I i z hz g hbase hg⟩

/-- Every reduced length-five closed subscheme in geometric general position
has the exact minimal self-dual five-quadric resolution of its actual ideal. -/
theorem reduced_projective_five_free_resolution
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} [AlgebraicGeometry.IsReduced Z]
    (i : Z ⟶ scheme I) [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    (hlen : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 5)
    (hp : ProjectiveGeometricGeneralPosition I i) :
    Nonempty (FiveQuadricResolution K (projectiveSubschemeIdeal I i).toIdeal) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  have : Module.Finite K Γ(Z, ⊤) := finiteSchemeCoefficient_finite (i ≫ toBase I)
  obtain ⟨p, hgp, he⟩ := reduced_projective_general_position_coordinates I i hp
  rw [he]
  exact reduced_five_algebra_free_resolution
    ((finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hlen) p hgp

/-- The actual homogeneous coordinate ring of a reduced length-five closed
subscheme in geometric general position is Gorenstein. -/
theorem reduced_projective_five_homogeneous_gorenstein
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} [AlgebraicGeometry.IsReduced Z]
    (i : Z ⟶ scheme I) [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    (hlen : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 5)
    (hp : ProjectiveGeometricGeneralPosition I i) :
    IsNoetherianRing (MvPolynomial (Fin 4) K ⧸ (projectiveSubschemeIdeal I i).toIdeal) ∧
      HasInjectiveDimensionLE
        (ModuleCat.of (MvPolynomial (Fin 4) K ⧸ (projectiveSubschemeIdeal I i).toIdeal)
          (MvPolynomial (Fin 4) K ⧸ (projectiveSubschemeIdeal I i).toIdeal)) 1 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  have : Module.Finite K Γ(Z, ⊤) := finiteSchemeCoefficient_finite (i ≫ toBase I)
  obtain ⟨p, hgp, he⟩ := reduced_projective_general_position_coordinates I i hp
  rw [he]
  exact reduced_five_algebra_homogeneous_gorenstein
    ((finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hlen) p hgp

/-- A homogeneous cubic containing an actual reduced length-five closed
subscheme in geometric general position has a ground-field Pfaffian presentation. -/
theorem reduced_projective_five_polynomial_presentation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} [AlgebraicGeometry.IsReduced Z]
    (i : Z ⟶ scheme I) [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    (hlen : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 5)
    (hp : ProjectiveGeometricGeneralPosition I i)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3) (hI : f ∈ I.toIdeal) :
    ∃ P : Fin 4 → Mat K 6, (∀ j, IsAlternating (P j)) ∧
      (pfaffianCubic P).toMvPolynomial = f := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  have : Module.Finite K Γ(Z, ⊤) := finiteSchemeCoefficient_finite (i ≫ toBase I)
  obtain ⟨p, hgp, he⟩ := reduced_projective_general_position_coordinates I i hp
  apply reduced_five_algebra_polynomial_presentation
    ((finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hlen) p hgp f hf
  apply (mem_algebraVectorIdeal_of_homogeneous p f hf).mp
  rw [← he]
  change f ∈ projectiveSubschemeIdeal I i
  rw [mem_projectiveSubschemeIdeal]
  intro x
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hI]
  exact Ideal.zero_mem _

/-- Lemma 4.1 on the actual cubic hypersurface and actual length-five closed
subscheme. Smoothness is not needed for the Pfaffian presentation. -/
theorem reduced_length_five_subscheme_pfaffian
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    {Z : Scheme.{u}} [AlgebraicGeometry.IsReduced Z]
    (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hlen : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase f hf) = 5)
    (hp : ProjectiveGeometricGeneralPosition (equationIdeal f hf) i) :
    ∃ P : Fin 4 → Mat K 6, (∀ j, IsAlternating (P j)) ∧
      (pfaffianCubic P).toMvPolynomial = f := by
  let i' : Z ⟶ scheme (equationIdeal f hf) := i
  have : IsClosedImmersion i' := inferInstanceAs (IsClosedImmersion i)
  have : IsFinite (i' ≫ toBase (equationIdeal f hf)) :=
    inferInstanceAs (IsFinite (i ≫ hypersurfaceToBase f hf))
  exact reduced_projective_five_polynomial_presentation (equationIdeal f hf) i' hlen hp
    f hf (Ideal.subset_span (Set.mem_singleton f))

end
end PfaffianDescent
