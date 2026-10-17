import AllCharacteristics.DisjointClosedUnion
import AllCharacteristics.FiniteSubschemeFromImmersion
import AllCharacteristics.FiniteSubschemeRank
import Mathlib.AlgebraicGeometry.Limits

/-!
# Disjoint unions of affine finite subschemes

Two disjoint affine finite-flat closed subschemes over a field have an
ideal-defined union.  Its coordinate algebra is the product of the two
coordinate algebras, so its rank is the sum of their ranks.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u

/-- The affine scheme underlying the disjoint union of two affine schemes,
followed by their given maps to the ambient scheme. -/
noncomputable def disjointSpecUnionMap
    {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) :
    Spec (.of (A × B)) ⟶ X :=
  (asIso (coprodSpec A B)).inv ≫ coprod.desc i j

/-- The image of the affine product-coordinate presentation of a disjoint
union is contained in the union of the images of its two components. -/
theorem range_disjointSpecUnionMap_subset
    {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) :
    Set.range (disjointSpecUnionMap i j) ⊆ Set.range i ∪ Set.range j := by
  rintro _ ⟨x, rfl⟩
  let e := asIso (coprodSpec A B)
  obtain ⟨(a | b), h⟩ :=
    (coprodMk (Spec (.of A)) (Spec (.of B))).surjective (e.inv x)
  · left
    refine ⟨a, ?_⟩
    change i a = (coprod.desc i j) (e.inv x)
    rw [← h, coprodMk_inl]
    exact congrArg (fun k : Spec (.of A) ⟶ X => k a) (coprod.inl_desc i j).symm
  · right
    refine ⟨b, ?_⟩
    change j b = (coprod.desc i j) (e.inv x)
    rw [← h, coprodMk_inr]
    exact congrArg (fun k : Spec (.of B) ⟶ X => k b) (coprod.inr_desc i j).symm

/-- Each point of the left component remains a point of the affine
product-coordinate presentation of the disjoint union. -/
theorem range_left_subset_range_disjointSpecUnionMap
    {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) :
    Set.range i ⊆ Set.range (disjointSpecUnionMap i j) := by
  rintro _ ⟨a, rfl⟩
  let e := asIso (coprodSpec A B)
  refine ⟨e.hom ((coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B)).base a), ?_⟩
  change (coprod.desc i j) (e.inv (e.hom
    ((coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B)).base a))) = i a
  have hcancel : e.inv (e.hom
      ((coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B)).base a)) =
      (coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B)).base a := by
    exact congrArg (fun k : Spec (.of A) ⨿ Spec (.of B) ⟶
        Spec (.of A) ⨿ Spec (.of B) =>
      k.base ((coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B)).base a))
      e.hom_inv_id
  rw [hcancel]
  exact congrArg (fun k : Spec (.of A) ⟶ X => k.base a) (coprod.inl_desc i j)

/-- Each point of the right component remains a point of the affine
product-coordinate presentation of the disjoint union. -/
theorem range_right_subset_range_disjointSpecUnionMap
    {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) :
    Set.range j ⊆ Set.range (disjointSpecUnionMap i j) := by
  rintro _ ⟨b, rfl⟩
  let e := asIso (coprodSpec A B)
  refine ⟨e.hom ((coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B)).base b), ?_⟩
  change (coprod.desc i j) (e.inv (e.hom
    ((coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B)).base b))) = j b
  have hcancel : e.inv (e.hom
      ((coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B)).base b)) =
      (coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B)).base b := by
    exact congrArg (fun k : Spec (.of A) ⨿ Spec (.of B) ⟶
        Spec (.of A) ⨿ Spec (.of B) =>
      k.base ((coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B)).base b))
      e.hom_inv_id
  rw [hcancel]
  exact congrArg (fun k : Spec (.of B) ⟶ X => k.base b) (coprod.inr_desc i j)

/-- The image of the product-coordinate presentation is exactly the union
of the images of its two components. -/
theorem range_disjointSpecUnionMap_eq
    {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) :
    Set.range (disjointSpecUnionMap i j) = Set.range i ∪ Set.range j := by
  apply Set.Subset.antisymm
  · exact range_disjointSpecUnionMap_subset i j
  · rintro x (hx | hx)
    · exact range_left_subset_range_disjointSpecUnionMap i j hx
    · exact range_right_subset_range_disjointSpecUnionMap i j hx

/-- A map disjoint from each component is disjoint from their affine
product-coordinate union. -/
theorem disjoint_disjointSpecUnionMap_range_of_disjoint
    {A B : Type u} [CommRing A] [CommRing B] {X Y : Scheme.{u}}
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) (l : Y ⟶ X)
    (hi : Disjoint (Set.range i) (Set.range l))
    (hj : Disjoint (Set.range j) (Set.range l)) :
    Disjoint (Set.range (disjointSpecUnionMap i j)) (Set.range l) := by
  rw [Set.disjoint_left] at hi hj ⊢
  intro x hx hl
  obtain hxi | hxj := range_disjointSpecUnionMap_subset i j hx
  · exact hi hxi hl
  · exact hj hxj hl

theorem disjointSpecUnionMap_toBase
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B))) :
    disjointSpecUnionMap i j ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k (A × B))) := by
  rw [disjointSpecUnionMap, Category.assoc, coprod.desc_comp, hi, hj]
  calc
    (asIso (coprodSpec A B)).inv ≫
        coprod.desc (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k B))) =
        (asIso (coprodSpec A B)).inv ≫
          ((asIso (coprodSpec A B)).hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap k (A × B)))) := by
      congr 1
      apply coprod.hom_ext
      · rw [coprod.inl_desc]
        change Spec.map (CommRingCat.ofHom (algebraMap k A)) =
          coprod.inl ≫ coprodSpec A B ≫
            Spec.map (CommRingCat.ofHom (algebraMap k (A × B)))
        rw [coprodSpec_inl_assoc, ← Spec.map_comp]
        rw [Spec.map_inj]
        ext x
        simp
      · rw [coprod.inr_desc]
        change Spec.map (CommRingCat.ofHom (algebraMap k B)) =
          coprod.inr ≫ coprodSpec A B ≫
            Spec.map (CommRingCat.ofHom (algebraMap k (A × B)))
        rw [coprodSpec_inr_assoc, ← Spec.map_comp]
        rw [Spec.map_inj]
        ext x
        simp
    _ = Spec.map (CommRingCat.ofHom (algebraMap k (A × B))) := by simp

/-- Two disjoint closed immersions have a closed-immersion coproduct. -/
theorem isClosedImmersion_coprodDesc_of_disjoint
    {U V X : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hij : Disjoint (Set.range i) (Set.range j)) :
    IsClosedImmersion (coprod.desc i j) := by
  let Y : ULift.{u} WalkingPair → Scheme.{u} :=
    fun a => a.1.casesOn U V
  let a : ∀ b, Y b ⟶ X := fun b => match b with
    | ⟨.left⟩ => i
    | ⟨.right⟩ => j
  have hclosed : ∀ b, IsClosedImmersion (a b) := by
    rintro ⟨b⟩
    cases b <;> exact inferInstance
  have hdisjoint : Pairwise fun b c =>
      Disjoint (Set.range (a b).base) (Set.range (a c).base) := by
    rintro ⟨b⟩ ⟨c⟩ hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hij
    · exact hij.symm
    · exact (hbc rfl).elim
  have hclosedI : ∀ b, IsClosedImmersion (a b) := hclosed
  let e := coprodIsoSigma U V
  have hleft : coprod.inl ≫ e.hom = Sigma.ι Y ⟨WalkingPair.left⟩ := by
    dsimp [e]
    rw [← ι_left_coprodIsoSigma_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hright : coprod.inr ≫ e.hom = Sigma.ι Y ⟨WalkingPair.right⟩ := by
    dsimp [e]
    rw [← ι_right_coprodIsoSigma_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have heq : coprod.desc i j = e.hom ≫ Sigma.desc a := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc, ← Category.assoc, hleft, Sigma.ι_desc]
    · rw [coprod.inr_desc, ← Category.assoc, hright, Sigma.ι_desc]
  rw [heq]
  exact @IsClosedImmersion.comp _ _ _ e.hom (Sigma.desc a) inferInstance
    (@isClosedImmersion_sigmaDesc_of_disjoint _ _ _ _ _ a hclosedI hdisjoint)

/-- The affine map from the product coordinate algebra is a closed immersion
whenever its two components are disjoint closed immersions. -/
theorem isClosedImmersion_disjointSpecUnionMap
    {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hij : Disjoint (Set.range i) (Set.range j)) :
    IsClosedImmersion (disjointSpecUnionMap i j) := by
  rw [disjointSpecUnionMap]
  exact @IsClosedImmersion.comp _ _ _ (asIso (coprodSpec A B)).inv (coprod.desc i j)
    inferInstance (isClosedImmersion_coprodDesc_of_disjoint i j hij)

/-- The rank of the product-coordinate union is the sum of the component
ranks.  Closedness is not needed for this numerical calculation. -/
theorem finrank_disjointSpecUnionMap
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Module.Finite k A] [Module.Finite k B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (m n : ℕ)
    (hmi : (i ≫ f).finrank (IsLocalRing.closedPoint k) = m)
    (hnj : (j ≫ f).finrank (IsLocalRing.closedPoint k) = n) :
    (disjointSpecUnionMap i j ≫ f).finrank (IsLocalRing.closedPoint k) = m + n := by
  have hbase := disjointSpecUnionMap_toBase f i j hi hj
  have hmi' : Module.rankAtStalk (R := k) A (IsLocalRing.closedPoint k) = m := by
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap, ← hi]
    exact hmi
  have hnj' : Module.rankAtStalk (R := k) B (IsLocalRing.closedPoint k) = n := by
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap, ← hj]
    exact hnj
  rw [hbase, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_prod]
  change Module.rankAtStalk (R := k) A (IsLocalRing.closedPoint k) +
    Module.rankAtStalk (R := k) B (IsLocalRing.closedPoint k) = m + n
  rw [hmi', hnj']

/-- The union of two disjoint affine finite-flat closed subschemes over a
field is an ideal-defined finite subscheme whose rank is the sum of the two
component ranks. -/
noncomputable def finiteSubschemeDatumOfDisjointSpecUnion
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Module.Finite k A] [Module.Finite k B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (m n : ℕ)
    (hmi : (i ≫ f).finrank (IsLocalRing.closedPoint k) = m)
    (hnj : (j ≫ f).finrank (IsLocalRing.closedPoint k) = n)
    (hij : Disjoint (Set.range i) (Set.range j)) :
    FiniteSubschemeDatum f (m + n) := by
  let q := disjointSpecUnionMap i j
  haveI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
  have hqbase : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (A × B))) :=
    disjointSpecUnionMap_toBase f i j hi hj
  haveI : IsFinite (q ≫ f) := by
    rw [hqbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : Flat (q ≫ f) := by
    rw [hqbase]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Module.FinitePresentation k (A × B) :=
    Module.finitePresentation_of_finite k (A × B)
  haveI : Algebra.FinitePresentation k (A × B) :=
    Algebra.FinitePresentation.of_finitePresentation k (A × B)
  haveI : LocallyOfFinitePresentation (q ≫ f) := by
    rw [hqbase]
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hmi' : Module.rankAtStalk (R := k) A (IsLocalRing.closedPoint k) = m := by
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap, ← hi]
    exact hmi
  have hnj' : Module.rankAtStalk (R := k) B (IsLocalRing.closedPoint k) = n := by
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap, ← hj]
    exact hnj
  exact finiteSubschemeDatumOfClosedImmersion q f (m + n) (fun s => by
    have hs : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst s
    rw [hqbase, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_prod]
    change Module.rankAtStalk (R := k) A (IsLocalRing.closedPoint k) +
      Module.rankAtStalk (R := k) B (IsLocalRing.closedPoint k) = m + n
    rw [hmi', hnj'])

/-- The canonical affine presentation of the finite datum formed from a
disjoint union has exactly the union of the two original supports. -/
theorem range_finiteSubschemeDatumSpecMap_finiteSubschemeDatumOfDisjointSpecUnion
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Module.Finite k A] [Module.Finite k B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (m n : ℕ)
    (hmi : (i ≫ f).finrank (IsLocalRing.closedPoint k) = m)
    (hnj : (j ≫ f).finrank (IsLocalRing.closedPoint k) = n)
    (hij : Disjoint (Set.range i) (Set.range j)) :
    Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfDisjointSpecUnion f i j hi hj m n hmi hnj hij)) =
      Set.range i ∪ Set.range j := by
  let q := disjointSpecUnionMap i j
  haveI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
  have hqbase : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (A × B))) :=
    disjointSpecUnionMap_toBase f i j hi hj
  haveI : IsFinite (q ≫ f) := by
    rw [hqbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : Flat (q ≫ f) := by
    rw [hqbase]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Module.FinitePresentation k (A × B) :=
    Module.finitePresentation_of_finite k (A × B)
  haveI : Algebra.FinitePresentation k (A × B) :=
    Algebra.FinitePresentation.of_finitePresentation k (A × B)
  haveI : LocallyOfFinitePresentation (q ≫ f) := by
    rw [hqbase]
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hqrank : ∀ s : Spec (.of k), (q ≫ f).finrank s = m + n := by
    intro s
    have hs : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst s
    exact finrank_disjointSpecUnionMap f i j hi hj m n hmi hnj
  change Set.range (finiteSubschemeDatumSpecMap f
    (finiteSubschemeDatumOfClosedImmersion q f (m + n) hqrank)) = _
  rw [range_finiteSubschemeDatumSpecMap_finiteSubschemeDatumOfClosedImmersion]
  exact range_disjointSpecUnionMap_eq i j

/-- Iterating the binary construction gives the actual union of three
components.  The third component is required to be disjoint from the first
union, which is precisely the scheme-theoretic condition used in applications. -/
noncomputable def finiteSubschemeDatumOfThreeDisjointSpecUnion
    {k A B C : Type u} [Field k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) (l : Spec (.of C) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion l]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (hl : l ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k C)))
    (m n p : ℕ)
    (hmi : (i ≫ f).finrank (IsLocalRing.closedPoint k) = m)
    (hnj : (j ≫ f).finrank (IsLocalRing.closedPoint k) = n)
    (hpl : (l ≫ f).finrank (IsLocalRing.closedPoint k) = p)
    (hij : Disjoint (Set.range i) (Set.range j))
    (hijl : Disjoint (Set.range (disjointSpecUnionMap i j)) (Set.range l)) :
    FiniteSubschemeDatum f (m + n + p) := by
  let q := disjointSpecUnionMap i j
  haveI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
  have hqbase : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (A × B))) :=
    disjointSpecUnionMap_toBase f i j hi hj
  have hqrank : (q ≫ f).finrank (IsLocalRing.closedPoint k) = m + n := by
    exact finrank_disjointSpecUnionMap f i j hi hj m n hmi hnj
  exact finiteSubschemeDatumOfDisjointSpecUnion f q l hqbase hl (m + n) p hqrank hpl hijl

/-- The canonical affine presentation of an iterated disjoint union has
exactly the union of all three component supports. -/
theorem range_finiteSubschemeDatumSpecMap_finiteSubschemeDatumOfThreeDisjointSpecUnion
    {k A B C : Type u} [Field k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X) (l : Spec (.of C) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion l]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (hl : l ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k C)))
    (m n p : ℕ)
    (hmi : (i ≫ f).finrank (IsLocalRing.closedPoint k) = m)
    (hnj : (j ≫ f).finrank (IsLocalRing.closedPoint k) = n)
    (hpl : (l ≫ f).finrank (IsLocalRing.closedPoint k) = p)
    (hij : Disjoint (Set.range i) (Set.range j))
    (hijl : Disjoint (Set.range (disjointSpecUnionMap i j)) (Set.range l)) :
    Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfThreeDisjointSpecUnion f i j l hi hj hl m n p
        hmi hnj hpl hij hijl)) = Set.range i ∪ Set.range j ∪ Set.range l := by
  let q := disjointSpecUnionMap i j
  haveI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
  have hqbase : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (A × B))) :=
    disjointSpecUnionMap_toBase f i j hi hj
  have hqrank : (q ≫ f).finrank (IsLocalRing.closedPoint k) = m + n :=
    finrank_disjointSpecUnionMap f i j hi hj m n hmi hnj
  change Set.range (finiteSubschemeDatumSpecMap f
    (finiteSubschemeDatumOfDisjointSpecUnion f q l hqbase hl (m + n) p
      hqrank hpl hijl)) = _
  rw [range_finiteSubschemeDatumSpecMap_finiteSubschemeDatumOfDisjointSpecUnion]
  rw [range_disjointSpecUnionMap_eq i j]

end AllCharacteristics
