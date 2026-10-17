import AllCharacteristics.FiniteEtaleGaloisPoints
import AllCharacteristics.ProjectiveGaloisStableConfiguration
import AllCharacteristics.FiniteSubschemeRank
import PfaffianDescent.FiniteSchemeGeometricPoints
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Finite étale subschemes as rational projective configurations

A finite étale subscheme is split over a finite Galois extension into its
distinct geometric points.  The Galois group permutes those points, so their
ordered configuration descends through the symmetric-group quotient.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u v

lemma specMap_comp_finiteSchemeGeometricPoint
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) [IsFinite p] [IsAffine Z]
    (g : L ≃ₐ[K] L) :
    letI := PfaffianDescent.finiteSchemeCoefficientAlgebra p
    ∀ ev : Γ(Z, ⊤) →ₐ[K] L,
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          PfaffianDescent.finiteSchemeGeometricPoint p ev =
        PfaffianDescent.finiteSchemeGeometricPoint p (g.toAlgHom.comp ev) := by
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra p
  intro ev
  unfold PfaffianDescent.finiteSchemeGeometricPoint
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

variable {R : Type u} [CommRing R] {σ : Type v} [SetLike σ R] [AddSubgroupClass σ R]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every finite étale rank-`n` subscheme of a projective family over a
characteristic-zero field determines a rational point of the unordered
configuration quotient.  This includes disconnected finite étale schemes. -/
theorem exists_projectiveConfigurationPoint_of_finiteEtaleSubscheme
    {K : Type u} [Field K] [CharZero K]
    (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ) (D : FiniteSubschemeDatum f n)
    [Etale (D.val.subschemeι ≫ f)] :
    ∃ c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme,
      c ≫ projectiveConfigurationQuotientToBase 𝒜 f n = 𝟙 _ := by
  let p : D.val.subscheme ⟶ Spec (.of K) := D.val.subschemeι ≫ f
  letI : IsFinite p := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom p
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra p
  let A := Γ(D.val.subscheme, ⊤)
  haveI hfinite : Module.Finite K A :=
    PfaffianDescent.finiteSchemeCoefficient_finite p
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [PfaffianDescent.finiteSchemeCoefficient_spec p]
    infer_instance
  have hring : (algebraMap K A).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  haveI hetale : Algebra.Etale K A := RingHom.etale_algebraMap.mp hring
  have hn : Module.finrank K A = n := by
    change Module.finrank K Γ(D.val.subscheme, ⊤) = n
    rw [PfaffianDescent.finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank f D
  obtain ⟨L, hLfield, hLalg, hLfinite, hLgalois, ⟨e⟩⟩ :=
    exists_finiteGalois_splitAlgEquivFin K A n hn
  letI : Field L := hLfield
  letI : Algebra K L := hLalg
  letI : FiniteDimensional K L := hLfinite
  letI : IsGalois K L := hLgalois
  let q : Fin n → (Spec (.of L) ⟶ Proj 𝒜) := fun i ↦
    PfaffianDescent.finiteSchemeGeometricPoint p (splitAlgHom K A L e i) ≫
      D.val.subschemeι
  have hq : ∀ i, q i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ (𝟙 _) := by
    intro i
    dsimp only [q]
    rw [Category.assoc]
    change PfaffianDescent.finiteSchemeGeometricPoint p
        (splitAlgHom K A L e i) ≫ p = _
    rw [PfaffianDescent.finiteSchemeGeometricPoint_over_base]
    simp
  have hdist : ∀ i j, i ≠ j → q i ≠ q j := by
    intro i j hij heq
    apply hij
    apply splitAlgHom_injective K A L e
    apply PfaffianDescent.finiteSchemeGeometricPoint_injective p
    apply (cancel_mono D.val.subschemeι).mp
    exact heq
  let τ : (L ≃ₐ[K] L) → Equiv.Perm (Fin n) := fun g ↦
    splitAlgHomGaloisPerm K A L e hn g
  have hτ : ∀ (g : L ≃ₐ[K] L) (i : Fin n),
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ q i = q (τ g i) := by
    intro g i
    dsimp only [q]
    rw [← Category.assoc, specMap_comp_finiteSchemeGeometricPoint]
    rw [splitAlgHom_galoisPerm K A L e hn g i]
  exact exists_projectiveConfigurationPoint_of_galoisStableTuple
    𝒜 f n (𝟙 _) q hq hdist τ hτ

/-- A finite étale rank-`n` subscheme makes the ordered distinct-configuration
space nonempty.  The finite étale datum first gives a rational point of the
unordered quotient; surjectivity of the quotient map then supplies a
geometric point of the ordered configuration space. -/
theorem nonempty_orderedFamilyConfigurationOver_of_finiteEtaleSubscheme
    {K : Type u} [Field K] [CharZero K]
    (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ) (D : FiniteSubschemeDatum f n)
    [Etale (D.val.subschemeι ≫ f)] :
    Nonempty (orderedFamilyConfigurationOver f n).left := by
  obtain ⟨c, -⟩ :=
    exists_projectiveConfigurationPoint_of_finiteEtaleSubscheme 𝒜 f n D
  obtain ⟨a, -⟩ := (projectiveConfigurationQuotientMap 𝒜 f n).surjective
    (c (IsLocalRing.closedPoint K))
  exact ⟨a⟩

/-- A finite étale subscheme on a field-valued base change of a projective
family determines the corresponding field-valued point of the original
unordered configuration quotient. -/
theorem exists_projectiveConfigurationPoint_of_finiteEtaleSubscheme_baseChange
    {S X : Scheme.{u}} [IsAffine S]
    (f : Proj 𝒜 ⟶ S) [IsSeparated f]
    {K : Type u} [Field K] [CharZero K]
    (b : Spec (.of K) ⟶ S) (g : X ⟶ Proj 𝒜)
    (pX : X ⟶ Spec (.of K))
    (hpb : IsPullback g pX f b)
    (n : ℕ) (D : FiniteSubschemeDatum pX n)
    (hEt : Etale (D.val.subschemeι ≫ pX)) :
    ∃ c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme,
      c ≫ projectiveConfigurationQuotientToBase 𝒜 f n = b := by
  letI : Etale (D.val.subschemeι ≫ pX) := hEt
  let p : D.val.subscheme ⟶ Spec (.of K) := D.val.subschemeι ≫ pX
  letI : IsFinite p := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom p
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra p
  let A := Γ(D.val.subscheme, ⊤)
  haveI hfinite : Module.Finite K A :=
    PfaffianDescent.finiteSchemeCoefficient_finite p
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [PfaffianDescent.finiteSchemeCoefficient_spec p]
    infer_instance
  have hring : (algebraMap K A).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  haveI hetale : Algebra.Etale K A := RingHom.etale_algebraMap.mp hring
  have hn : Module.finrank K A = n := by
    change Module.finrank K Γ(D.val.subscheme, ⊤) = n
    rw [PfaffianDescent.finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank pX D
  obtain ⟨L, hLfield, hLalg, hLfinite, hLgalois, ⟨e⟩⟩ :=
    exists_finiteGalois_splitAlgEquivFin K A n hn
  letI : Field L := hLfield
  letI : Algebra K L := hLalg
  letI : FiniteDimensional K L := hLfinite
  letI : IsGalois K L := hLgalois
  let q : Fin n → (Spec (.of L) ⟶ Proj 𝒜) := fun i ↦
    PfaffianDescent.finiteSchemeGeometricPoint p (splitAlgHom K A L e i) ≫
      D.val.subschemeι ≫ g
  have hq : ∀ i, q i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b := by
    intro i
    dsimp only [q]
    simp only [Category.assoc]
    rw [hpb.w]
    change
      (PfaffianDescent.finiteSchemeGeometricPoint p
        (splitAlgHom K A L e i) ≫ p) ≫ b = _
    rw [PfaffianDescent.finiteSchemeGeometricPoint_over_base]
  have hdist : ∀ i j, i ≠ j → q i ≠ q j := by
    intro i j hij heq
    apply hij
    apply splitAlgHom_injective K A L e
    apply PfaffianDescent.finiteSchemeGeometricPoint_injective p
    apply (cancel_mono D.val.subschemeι).mp
    apply hpb.hom_ext
    · simpa only [q, Category.assoc] using heq
    · change
        PfaffianDescent.finiteSchemeGeometricPoint p
            (splitAlgHom K A L e i) ≫ p =
          PfaffianDescent.finiteSchemeGeometricPoint p
            (splitAlgHom K A L e j) ≫ p
      rw [PfaffianDescent.finiteSchemeGeometricPoint_over_base,
        PfaffianDescent.finiteSchemeGeometricPoint_over_base]
  let τ : (L ≃ₐ[K] L) → Equiv.Perm (Fin n) := fun h ↦
    splitAlgHomGaloisPerm K A L e hn h
  have hτ : ∀ (h : L ≃ₐ[K] L) (i : Fin n),
      Spec.map (CommRingCat.ofHom h.toRingHom) ≫ q i = q (τ h i) := by
    intro h i
    dsimp only [q]
    simp only [← Category.assoc]
    rw [specMap_comp_finiteSchemeGeometricPoint]
    rw [splitAlgHom_galoisPerm K A L e hn h i]
  exact exists_projectiveConfigurationPoint_of_galoisStableTuple
    𝒜 f n b q hq hdist τ hτ

end AllCharacteristics
