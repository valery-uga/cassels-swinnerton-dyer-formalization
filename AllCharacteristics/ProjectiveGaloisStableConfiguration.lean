import AllCharacteristics.ProjectiveGaloisOrbitConfiguration

/-!
# Galois-stable tuples as rational unordered configurations

This is the tuple form of Galois descent for projective configurations.  It
applies to the geometric points of a disconnected finite étale scheme as
well as to the conjugates of one closed point.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S]
variable (f : Proj 𝒜 ⟶ S) [IsSeparated f]

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- A pairwise-distinct tuple over a finite Galois extension which is
permuted by every Galois automorphism descends to a rational point of the
unordered configuration quotient.  The chosen ordered lift and all of its
coordinate equations are retained. -/
theorem exists_projectiveConfigurationPoint_of_galoisStableTuple_with_orderedLift
    (n : ℕ) (b : Spec (.of K) ⟶ S)
    (q : Fin n → (Spec (.of L) ⟶ Proj 𝒜))
    (hq : ∀ i, q i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b)
    (hdist : ∀ i j, i ≠ j → q i ≠ q j)
    (τ : (L ≃ₐ[K] L) → Equiv.Perm (Fin n))
    (hτ : ∀ (g : L ≃ₐ[K] L) (i : Fin n),
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ q i = q (τ g i)) :
    ∃ (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
      (a : Spec (.of L) ⟶ (orderedFamilyConfigurationOver f n).left),
      c ≫ projectiveConfigurationQuotientToBase 𝒜 f n = b ∧
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ c =
        a ≫ projectiveConfigurationQuotientMap 𝒜 f n ∧
      ∀ i : Fin n,
        a ≫ Over.Hom.left (orderedFamilyConfigurationι f n) ≫
            (orderedFamilyCoordinate f n i).left = q i := by
  let π : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let bL : Spec (.of L) ⟶ S := π ≫ b
  obtain ⟨a, haBase, haCoord⟩ :=
    exists_orderedConfigurationFieldPoint f n bL q hq hdist
  have hactionCoord (g : Equiv.Perm (Fin n)) (i : Fin n) :
      configurationRightAction f n g ≫
          Over.Hom.left (orderedFamilyConfigurationι f n) ≫
          (orderedFamilyCoordinate f n i).left =
        Over.Hom.left (orderedFamilyConfigurationι f n) ≫
          (orderedFamilyCoordinate f n (g i)).left := by
    change configurationRightAction f n g ≫
        (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left =
      (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n (g i)).left
    exact configurationRightAction_coordinate f n g i
  have haEquivariant (g : L ≃ₐ[K] L) :
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a =
        a ≫ configurationRightAction f n (τ g) := by
    let iC := Over.Hom.left (orderedFamilyConfigurationι f n)
    let w₁ : Spec (.of L) ⟶ (orderedFamilyPowerOver f n).left :=
      (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a) ≫ iC
    let w₂ : Spec (.of L) ⟶ (orderedFamilyPowerOver f n).left :=
      (a ≫ configurationRightAction f n (τ g)) ≫ iC
    have hw₁ : w₁ ≫ (orderedFamilyPowerOver f n).hom = bL := by
      dsimp only [w₁, iC]
      simp only [Category.assoc]
      rw [(orderedFamilyConfigurationι f n).w, haBase]
      dsimp only [bL, π]
      simpa only [Category.assoc] using
        congrArg (· ≫ b) (specMap_galois_comp_base (K := K) g)
    have hw₂ : w₂ ≫ (orderedFamilyPowerOver f n).hom = bL := by
      dsimp only [w₂, iC]
      simp only [Category.assoc]
      rw [(orderedFamilyConfigurationι f n).w, configurationRightAction_toBase, haBase]
    let t₁ : Over.mk bL ⟶ orderedFamilyPowerOver f n := Over.homMk w₁ hw₁
    let t₂ : Over.mk bL ⟶ orderedFamilyPowerOver f n := Over.homMk w₂ hw₂
    have ht : t₁ = t₂ := by
      apply orderedFamilyPower_coordinate_ext f (Over.mk bL) n
      intro i
      apply Over.OverMorphism.ext
      change w₁ ≫ (orderedFamilyCoordinate f n i).left =
        w₂ ≫ (orderedFamilyCoordinate f n i).left
      calc
        w₁ ≫ (orderedFamilyCoordinate f n i).left =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ q i := by
          dsimp only [w₁, iC]
          simpa only [Category.assoc] using
            congrArg (fun m ↦ Spec.map (CommRingCat.ofHom g.toRingHom) ≫ m) (haCoord i)
        _ = q (τ g i) := hτ g i
        _ = w₂ ≫ (orderedFamilyCoordinate f n i).left := by
          dsimp only [w₂, iC]
          rw [Category.assoc, Category.assoc, hactionCoord]
          exact (haCoord (τ g i)).symm
    apply (cancel_mono iC).mp
    exact congrArg Over.Hom.left ht
  let z : Spec (.of L) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
    a ≫ projectiveConfigurationQuotientMap 𝒜 f n
  obtain ⟨c, hc, -⟩ := existsUnique_finiteGaloisDescend K L z (by
    intro gs
    change Spec.map (CommRingCat.ofHom (Shrink.mulEquiv gs).toRingHom) ≫ z = z
    let g : L ≃ₐ[K] L := Shrink.mulEquiv gs
    calc
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ z =
          (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a) ≫
            projectiveConfigurationQuotientMap 𝒜 f n := by
        exact Category.assoc _ _ _ |>.symm
      _ = (a ≫ configurationRightAction f n (τ g)) ≫
            projectiveConfigurationQuotientMap 𝒜 f n := by
        exact congrArg (· ≫ projectiveConfigurationQuotientMap 𝒜 f n) (haEquivariant g)
      _ = a ≫ (configurationRightAction f n (τ g) ≫
            projectiveConfigurationQuotientMap 𝒜 f n) := Category.assoc _ _ _
      _ = z := by
        rw [projectiveConfigurationQuotientMap_invariant])
  refine ⟨c, a, ?_, hc, haCoord⟩
  haveI : Epi π := by
    dsimp only [π]
    exact epi_specMap_finiteGalois K L
  apply (cancel_epi π).mp
  calc
    π ≫ (c ≫ projectiveConfigurationQuotientToBase 𝒜 f n) =
        (π ≫ c) ≫ projectiveConfigurationQuotientToBase 𝒜 f n :=
      Category.assoc _ _ _ |>.symm
    _ = z ≫ projectiveConfigurationQuotientToBase 𝒜 f n :=
      congrArg (· ≫ projectiveConfigurationQuotientToBase 𝒜 f n) hc
    _ = a ≫ (projectiveConfigurationQuotientMap 𝒜 f n ≫
          projectiveConfigurationQuotientToBase 𝒜 f n) := Category.assoc _ _ _
    _ = bL := by rw [projectiveConfigurationQuotientMap_toBase, haBase]
    _ = π ≫ b := rfl

/-- The ground-field point supplied by a Galois-stable tuple, without
retaining the ordered lift. -/
theorem exists_projectiveConfigurationPoint_of_galoisStableTuple
    (n : ℕ) (b : Spec (.of K) ⟶ S)
    (q : Fin n → (Spec (.of L) ⟶ Proj 𝒜))
    (hq : ∀ i, q i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ b)
    (hdist : ∀ i j, i ≠ j → q i ≠ q j)
    (τ : (L ≃ₐ[K] L) → Equiv.Perm (Fin n))
    (hτ : ∀ (g : L ≃ₐ[K] L) (i : Fin n),
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ q i = q (τ g i)) :
    ∃ c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme,
      c ≫ projectiveConfigurationQuotientToBase 𝒜 f n = b := by
  obtain ⟨c, a, hc, hca, hcoord⟩ :=
    exists_projectiveConfigurationPoint_of_galoisStableTuple_with_orderedLift
      𝒜 f n b q hq hdist τ hτ
  exact ⟨c, hc⟩

end AllCharacteristics
