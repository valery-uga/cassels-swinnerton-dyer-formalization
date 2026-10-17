import AllCharacteristics.FiniteSubschemeRank

/-!
# Pushing finite subschemes through closed immersions

An ideal-defined finite flat subscheme of a closed projective subvariety is
also an ideal-defined finite flat subscheme of the ambient projective scheme.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

/-- Transport ideal-defined finite subscheme data through a closed immersion
of ambient schemes. -/
noncomputable def finiteSubschemeDatum_pushforwardClosedImmersion
    {K : Type u} [Field K] {Y X : Scheme.{u}}
    (g : Y ⟶ X) [IsClosedImmersion g] (f : X ⟶ Spec (.of K))
    {n : ℕ} (D : FiniteSubschemeDatum (g ≫ f) n) :
    FiniteSubschemeDatum f n := by
  let i : D.val.subscheme ⟶ X := D.val.subschemeι ≫ g
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ f) := by
    change IsFinite ((D.val.subschemeι ≫ g) ≫ f)
    rw [Category.assoc]
    exact D.property.1
  haveI : Flat (i ≫ f) := by
    change Flat ((D.val.subschemeι ≫ g) ≫ f)
    rw [Category.assoc]
    exact D.property.2.1
  haveI : LocallyOfFinitePresentation (i ≫ f) := by
    change LocallyOfFinitePresentation ((D.val.subschemeι ≫ g) ≫ f)
    rw [Category.assoc]
    exact D.property.2.2.1
  exact finiteSubschemeDatumOfClosedImmersion i f n (fun s ↦ by
    change ((D.val.subschemeι ≫ g) ≫ f).finrank s = n
    rw [Category.assoc]
    exact D.property.2.2.2 s)

/-- The canonical affine presentation of a datum formed from a closed
immersion has image contained in the image of that immersion. -/
theorem finiteSubschemeDatumSpecMap_ofClosedImmersion_range_subset
    {K : Type u} [Field K] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of K))
    [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
    (n : ℕ) (hn : ∀ s : Spec (.of K), (i ≫ f).finrank s = n) :
    Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfClosedImmersion i f n hn)) ⊆ Set.range i := by
  let D := finiteSubschemeDatumOfClosedImmersion i f n hn
  let e := finiteSubschemeDatumOfClosedImmersionIso i f n hn
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  haveI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  have hι : e.hom ≫ D.val.subschemeι = i := by
    exact finiteSubschemeDatumOfClosedImmersionIso_hom_ι i f n hn
  have he : e.inv ≫ i = D.val.subschemeι := by
    calc
      e.inv ≫ i = e.inv ≫ (e.hom ≫ D.val.subschemeι) :=
        congrArg (fun k : Z ⟶ X => e.inv ≫ k) hι.symm
      _ = D.val.subschemeι := by simp
  have hmap : finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfClosedImmersion i f n hn) =
        D.val.subscheme.isoSpec.inv ≫ (e.inv ≫ i) := by
    change D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι =
      D.val.subscheme.isoSpec.inv ≫ (e.inv ≫ i)
    rw [he]
  rintro _ ⟨y, rfl⟩
  refine ⟨e.inv (D.val.subscheme.isoSpec.inv y), ?_⟩
  rw [hmap]
  rfl

/-- Pushing a datum through a closed immersion produces a canonical affine
presentation whose image stays inside the image of the ambient immersion. -/
theorem finiteSubschemeDatumSpecMap_pushforwardClosedImmersion_range_subset
    {K : Type u} [Field K] {Y X : Scheme.{u}}
    (g : Y ⟶ X) [IsClosedImmersion g] (f : X ⟶ Spec (.of K))
    {n : ℕ} (D : FiniteSubschemeDatum (g ≫ f) n) :
    Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatum_pushforwardClosedImmersion g f D)) ⊆ Set.range g := by
  let i : D.val.subscheme ⟶ X := D.val.subschemeι ≫ g
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ f) := by
    change IsFinite ((D.val.subschemeι ≫ g) ≫ f)
    rw [Category.assoc]
    exact D.property.1
  haveI : Flat (i ≫ f) := by
    change Flat ((D.val.subschemeι ≫ g) ≫ f)
    rw [Category.assoc]
    exact D.property.2.1
  haveI : LocallyOfFinitePresentation (i ≫ f) := by
    change LocallyOfFinitePresentation ((D.val.subschemeι ≫ g) ≫ f)
    rw [Category.assoc]
    exact D.property.2.2.1
  let hfinrank : ∀ s : Spec (.of K), (i ≫ f).finrank s = n := fun s ↦ by
    change ((D.val.subschemeι ≫ g) ≫ f).finrank s = n
    rw [Category.assoc]
    exact D.property.2.2.2 s
  let Dpush := finiteSubschemeDatumOfClosedImmersion i f n hfinrank
  have hi : Set.range (finiteSubschemeDatumSpecMap f Dpush) ⊆ Set.range i :=
    finiteSubschemeDatumSpecMap_ofClosedImmersion_range_subset i f n hfinrank
  change Set.range (finiteSubschemeDatumSpecMap f Dpush) ⊆ Set.range g
  intro x hx
  obtain ⟨z, hz⟩ := hi hx
  exact ⟨D.val.subschemeι z, hz⟩

/-- Disjointness from the image of a closed immersion keeps a datum disjoint
from every finite subscheme pushed through that immersion. -/
theorem finiteSubschemeDatum_disjoint_pushforwardClosedImmersion_of_disjoint_range
    {K : Type u} [Field K] {Y X : Scheme.{u}}
    (g : Y ⟶ X) [IsClosedImmersion g] (f : X ⟶ Spec (.of K))
    {m n : ℕ} (D₁ : FiniteSubschemeDatum f m) (D₂ : FiniteSubschemeDatum (g ≫ f) n)
    (h : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁)) (Set.range g)) :
    Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁))
      (Set.range (finiteSubschemeDatumSpecMap f
        (finiteSubschemeDatum_pushforwardClosedImmersion g f D₂))) := by
  rw [Set.disjoint_left] at h ⊢
  intro x hx hp
  exact h hx (finiteSubschemeDatumSpecMap_pushforwardClosedImmersion_range_subset
    g f D₂ hp)

/-- Any map disjoint from the image of a closed immersion is disjoint from
the canonical affine presentation of a datum pushed through that immersion. -/
theorem disjoint_range_pushforwardClosedImmersion_of_disjoint_range
    {K : Type u} [Field K] {Z Y X : Scheme.{u}}
    (i : Z ⟶ X) (g : Y ⟶ X) [IsClosedImmersion g] (f : X ⟶ Spec (.of K))
    {n : ℕ} (D : FiniteSubschemeDatum (g ≫ f) n)
    (h : Disjoint (Set.range i) (Set.range g)) :
    Disjoint (Set.range i)
      (Set.range (finiteSubschemeDatumSpecMap f
        (finiteSubschemeDatum_pushforwardClosedImmersion g f D))) := by
  rw [Set.disjoint_left] at h ⊢
  intro x hx hp
  exact h hx (finiteSubschemeDatumSpecMap_pushforwardClosedImmersion_range_subset
    g f D hp)

end AllCharacteristics
