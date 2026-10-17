import AllCharacteristics.FiniteGaloisInvariantDescent
import AllCharacteristics.GaloisEmbeddingEnumeration
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.OrderedConfigurationFieldPoints
import AllCharacteristics.OrderedConfigurationMarkedAction
import AllCharacteristics.ProjectiveConfigurationFactorization

/-!
# Galois orbits as rational unordered projective configurations

A closed point becomes the ordered tuple of its distinct embeddings in a
finite Galois splitting field.  The Galois action only permutes that tuple,
so its image in the actual unordered configuration quotient descends to the
ground field.  This is the descent step used in Voisin's generic-point
argument.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S]
variable (f : Proj 𝒜 ⟶ S) [IsSeparated f]

section
variable {K E L : Type u} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [FiniteDimensional K L] [IsGalois K L]

lemma specMap_embedding_comp_base (e : E →ₐ[K] L) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact e.commutes x

lemma specMap_galois_comp_base (g : L ≃ₐ[K] L) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact g.commutes

include L
/-- The conjugates of a finite separable point define a ground-field point
of the actual unordered projective configuration quotient.  The result also
retains the ordered lift over the splitting field, its quotient equation,
and all of its coordinate equations; these data identify the represented
finite cycle with the original closed point. -/
theorem exists_projectiveConfigurationPoint_of_galoisOrbit_with_orderedLift
    (n : ℕ) (hn : Module.finrank K E = n)
    (b : Spec (.of K) ⟶ S)
    (q : Spec (.of E) ⟶ Proj 𝒜) [IsClosedImmersion q]
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ b) :
    ∃ (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
      (a : Spec (.of L) ⟶ (orderedFamilyConfigurationOver f n).left),
      c ≫ projectiveConfigurationQuotientToBase 𝒜 f n = b ∧
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ c =
        a ≫ projectiveConfigurationQuotientMap 𝒜 f n ∧
      ∀ i : Fin n,
        a ≫ Over.Hom.left (orderedFamilyConfigurationι f n) ≫
            (orderedFamilyCoordinate f n i).left =
          Spec.map (CommRingCat.ofHom
            ((galoisEmbeddingIndex K E L n hn) i).toRingHom) ≫ q := by
  let e : Fin n ≃ (E →ₐ[K] L) := galoisEmbeddingIndex K E L n hn
  let π : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let bL : Spec (.of L) ⟶ S := π ≫ b
  let qL : Fin n → (Spec (.of L) ⟶ Proj 𝒜) := fun i ↦
    Spec.map (CommRingCat.ofHom (e i).toRingHom) ≫ q
  have hqL : ∀ i, qL i ≫ f = bL := by
    intro i
    dsimp only [qL, bL, π]
    rw [Category.assoc, hq, ← Category.assoc, specMap_embedding_comp_base]
  have hdist : ∀ i j, i ≠ j → qL i ≠ qL j := by
    intro i j hij heq
    have hm : Spec.map (CommRingCat.ofHom (e i).toRingHom) =
        Spec.map (CommRingCat.ofHom (e j).toRingHom) := by
      apply (cancel_mono q).mp
      exact heq
    have hr := Spec.map_injective hm
    apply hij
    apply e.injective
    apply AlgHom.ext
    intro x
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hr) x
  obtain ⟨a, haBase, haCoord⟩ :=
    exists_orderedConfigurationFieldPoint f n bL qL hqL hdist
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
        a ≫ configurationRightAction f n
          (galoisEmbeddingPermutation K E L n hn g) := by
    let τ := galoisEmbeddingPermutation K E L n hn g
    let iC := Over.Hom.left (orderedFamilyConfigurationι f n)
    let w₁ : Spec (.of L) ⟶ (orderedFamilyPowerOver f n).left :=
      (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a) ≫ iC
    let w₂ : Spec (.of L) ⟶ (orderedFamilyPowerOver f n).left :=
      (a ≫ configurationRightAction f n τ) ≫ iC
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
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ qL i := by
          dsimp only [w₁, iC]
          simpa only [Category.assoc] using
            congrArg (fun m ↦ Spec.map (CommRingCat.ofHom g.toRingHom) ≫ m) (haCoord i)
        _ = qL (τ i) := by
          dsimp only [qL, τ]
          rw [← Category.assoc, ← Spec.map_comp]
          have he := galoisEmbeddingIndex_permutation K E L n hn g i
          rw [he]
          rfl
        _ = w₂ ≫ (orderedFamilyCoordinate f n i).left := by
          dsimp only [w₂, iC]
          rw [Category.assoc, Category.assoc, hactionCoord]
          exact (haCoord (τ i)).symm
    apply (cancel_mono iC).mp
    exact congrArg Over.Hom.left ht
  let z : Spec (.of L) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
    a ≫ projectiveConfigurationQuotientMap 𝒜 f n
  obtain ⟨c, hc, -⟩ := existsUnique_finiteGaloisDescend K L z (by
    intro gs
    change Spec.map (CommRingCat.ofHom (Shrink.mulEquiv gs).toRingHom) ≫ z = z
    let g : L ≃ₐ[K] L := Shrink.mulEquiv gs
    let τ := galoisEmbeddingPermutation K E L n hn g
    calc
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ z =
          (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a) ≫
            projectiveConfigurationQuotientMap 𝒜 f n := by
        exact Category.assoc _ _ _ |>.symm
      _ = (a ≫ configurationRightAction f n τ) ≫
            projectiveConfigurationQuotientMap 𝒜 f n := by
        exact congrArg (· ≫ projectiveConfigurationQuotientMap 𝒜 f n) (haEquivariant g)
      _ = a ≫ (configurationRightAction f n τ ≫
            projectiveConfigurationQuotientMap 𝒜 f n) := Category.assoc _ _ _
      _ = z := by
        rw [projectiveConfigurationQuotientMap_invariant])
  refine ⟨c, a, ?_, ?_, ?_⟩
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
  · exact hc
  · intro i
    exact haCoord i

/-- The conjugates of a finite separable point define a ground-field point
of the actual unordered projective configuration quotient. -/
theorem exists_projectiveConfigurationPoint_of_galoisOrbit
    (n : ℕ) (hn : Module.finrank K E = n)
    (b : Spec (.of K) ⟶ S)
    (q : Spec (.of E) ⟶ Proj 𝒜) [IsClosedImmersion q]
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ b) :
    ∃ c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme,
      c ≫ projectiveConfigurationQuotientToBase 𝒜 f n = b := by
  obtain ⟨c, a, hc, hca, hcoord⟩ :=
    exists_projectiveConfigurationPoint_of_galoisOrbit_with_orderedLift
      𝒜 f (K := K) (E := E) (L := L) n hn b q hq
  exact ⟨c, hc⟩

end

section ClosedPoint
variable {K : Type u} [Field K] [CharZero K]

/-- Every closed point in a characteristic-zero projective family determines
a rational point of the unordered distinct-configuration space of the same
degree.  The finite Galois splitting field is constructed as a normal closure
inside an algebraic closure, rather than assumed. -/
theorem exists_projectiveConfigurationPoint_of_closedPoint
    (g : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated g] [LocallyOfFiniteType g]
    (x : closedPoints (Proj 𝒜)) (n : ℕ)
    (hx : g.residueDegree x.1 = n) :
    ∃ c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen 𝒜 g n).toScheme,
      c ≫ projectiveConfigurationQuotientToBase 𝒜 g n = 𝟙 _ := by
  let E : Type u := (Proj 𝒜).residueField x.1
  letI : Field E := inferInstanceAs (Field ((Proj 𝒜).residueField x.1))
  letI : Algebra K E := pointAlgebra g x.1
  haveI : FiniteDimensional K E := closedPoint_moduleFinite g x
  haveI : Algebra.IsSeparable K E := inferInstance
  let q : Spec (.of E) ⟶ Proj 𝒜 := (Proj 𝒜).fromSpecResidueField x.1
  haveI : IsClosedImmersion q := by
    dsimp only [q]
    exact isClosed_singleton_iff_isClosedImmersion.mp x.2
  have hn : Module.finrank K E = n :=
    (closedPoint_finrank_eq_residueDegree g x).trans hx
  let Ω : Type u := AlgebraicClosure K
  letI : Field Ω := inferInstanceAs (Field (AlgebraicClosure K))
  letI : Algebra K Ω := inferInstanceAs (Algebra K (AlgebraicClosure K))
  let ι : E →ₐ[K] Ω := IsAlgClosed.lift
  letI : Algebra E Ω := ι.toRingHom.toAlgebra
  letI : IsScalarTower K E Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (ι.commutes r).symm
  let L : Type u := IntermediateField.normalClosure K E Ω
  letI : Field L := inferInstanceAs (Field (IntermediateField.normalClosure K E Ω))
  letI : Algebra K L := inferInstanceAs (Algebra K (IntermediateField.normalClosure K E Ω))
  letI : Algebra E L := inferInstanceAs (Algebra E (IntermediateField.normalClosure K E Ω))
  letI : IsScalarTower K E L :=
    inferInstanceAs (IsScalarTower K E (IntermediateField.normalClosure K E Ω))
  letI : FiniteDimensional K L :=
    inferInstanceAs (FiniteDimensional K (IntermediateField.normalClosure K E Ω))
  letI : IsGalois K L :=
    inferInstanceAs (IsGalois K (IntermediateField.normalClosure K E Ω))
  apply exists_projectiveConfigurationPoint_of_galoisOrbit
    (𝒜 := 𝒜) g (K := K) (E := E) (L := L) n hn (𝟙 _) q
  simpa only [Category.comp_id] using (pointAlgebra_spec g x.1).symm

end ClosedPoint
end AllCharacteristics
