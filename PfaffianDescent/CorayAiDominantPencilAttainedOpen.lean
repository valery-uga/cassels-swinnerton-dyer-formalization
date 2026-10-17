import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import AllCharacteristics.UnirationalityCycle

/-! SOURCE ONLY. Chevalley supplies actual attained open sets. No attained-open,
second-point, image-dimension, member-integrality, or smaller-point premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
universe u v

private theorem constructible_generic_neighborhood_decision001
    {T : Type v} [TopologicalSpace T] (g : T)
    (hg : ∀ x : T, g ⤳ x) {S : Set T} (hS : IsConstructible S) :
    (g ∈ S → ∃ U : Set T, IsOpen U ∧ g ∈ U ∧ U ⊆ S) ∧
    (g ∉ S → ∃ U : Set T, IsOpen U ∧ g ∈ U ∧ U ⊆ Sᶜ) := by
  classical
  induction hS using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
      constructor
      · intro hgu
        exact ⟨U, hUopen, hgu, Set.Subset.rfl⟩
      · intro hgu
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ g, ?_⟩
        intro x hx hxu
        exact hgu ((hg x).mem_open hUopen hxu)
  | union S hS T hT ihS ihT =>
      constructor
      · intro hgST
        rcases hgST with hgS | hgT
        · obtain ⟨U, hU, hgU, hUS⟩ := ihS.1 hgS
          exact ⟨U, hU, hgU, hUS.trans Set.subset_union_left⟩
        · obtain ⟨U, hU, hgU, hUT⟩ := ihT.1 hgT
          exact ⟨U, hU, hgU, hUT.trans Set.subset_union_right⟩
      · intro hgST
        have hgS : g ∉ S := fun h => hgST (Or.inl h)
        have hgT : g ∉ T := fun h => hgST (Or.inr h)
        obtain ⟨U, hU, hgU, hUS⟩ := ihS.2 hgS
        obtain ⟨V, hV, hgV, hVT⟩ := ihT.2 hgT
        refine ⟨U ∩ V, hU.inter hV, ⟨hgU, hgV⟩, ?_⟩
        intro x hx hxST
        rcases hxST with hxS | hxT
        · exact hUS hx.1 hxS
        · exact hVT hx.2 hxT
  | compl S hS ih =>
      constructor
      · intro hgS
        exact ih.2 hgS
      · intro hgS
        have hgSin : g ∈ S := by simpa using hgS
        obtain ⟨U, hU, hgU, hUS⟩ := ih.1 hgSin
        exact ⟨U, hU, hgU, by simpa using hUS⟩

/-- A dense constructible subset contains an actual open neighborhood of
any point specializing to every point. The open subset is constructed,
not provided as an attainment certificate. -/
theorem dense_constructible_exists_generic_open001
    {T : Type v} [TopologicalSpace T] (g : T)
    (hg : ∀ x : T, g ⤳ x) (S : Set T)
    (hS : IsConstructible S) (hDense : Dense S) :
    ∃ U : Set T, IsOpen U ∧ g ∈ U ∧ U ⊆ S := by
  classical
  have hDecision := constructible_generic_neighborhood_decision001 g hg hS
  have hgS : g ∈ S := by
    by_contra hgS
    obtain ⟨U, hU, hgU, hUS⟩ := hDecision.2 hgS
    obtain ⟨x, hxU, hxS⟩ := hDense.inter_open_nonempty U hU ⟨g, hgU⟩
    exact hUS hxU hxS
  exact hDecision.1 hgS

/-- A genuine dominant finite-type morphism to an integral locally
Noetherian scheme attains an actual nonempty open of its target.
Chevalley is applied to the entire source, preserving its nilpotents. -/
theorem dominant_finiteType_exists_attained_generic_open001
    {X Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsDominant f] :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧ (V : Set Y) ⊆ Set.range f := by
  have hRange : IsConstructible (Set.range f) := by
    simpa only [Set.image_univ] using
      f.isConstructible_image (IsConstructible.univ (X := X))
  obtain ⟨U, hU, hgU, hURange⟩ :=
    dense_constructible_exists_generic_open001 (genericPoint Y)
      (fun x => genericPoint_specializes x) (Set.range f) hRange f.denseRange
  exact ⟨⟨U, hU⟩, hgU, hURange⟩

/-- Over an infinite field, a dominant finite-type morphism to affine
space attains an actual ground-field rational point. Applied to the
pencil map after removing the entire original image point, this
constructs a parameter attained away from that point. -/
theorem dominant_affineSpace_exists_attained_rational_section001
    {K σ : Type u} [Field K] [Infinite K] [Finite σ]
    {X : Scheme.{u}}
    (f : X ⟶ AffineSpace σ (Spec (.of K)))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f] :
    ∃ q : Spec (.of K) ⟶ AffineSpace σ (Spec (.of K)),
      q ≫ (AffineSpace σ (Spec (.of K)) ↘ Spec (.of K)) = 𝟙 _ ∧
      ∃ x : X, f x = q (IsLocalRing.closedPoint K) := by
  letI : IsNoetherianRing (MvPolynomial σ K) := inferInstance
  letI : IsLocallyNoetherian (Spec (.of (MvPolynomial σ K))) := inferInstance
  letI : IsLocallyNoetherian (AffineSpace σ (Spec (.of K))) :=
    LocallyOfFiniteType.isLocallyNoetherian (AffineSpace.SpecIso σ (.of K)).hom
  obtain ⟨V, hgV, hVRange⟩ := dominant_finiteType_exists_attained_generic_open001 f
  have hVDense : Dense (V : Set (AffineSpace σ (Spec (.of K)))) :=
    V.2.dense ⟨genericPoint _, hgV⟩
  obtain ⟨qV, hqV⟩ :=
    AllCharacteristics.HomogeneousProjective.dense_open_affineSpace_has_rational_section V hVDense
  refine ⟨qV ≫ V.ι, ?_, ?_⟩
  · simpa only [Category.assoc] using hqV
  · apply hVRange
    change (V.ι (qV (IsLocalRing.closedPoint K))) ∈ (V : Set _)
    exact (qV (IsLocalRing.closedPoint K)).property

end PfaffianDescent.Coray
