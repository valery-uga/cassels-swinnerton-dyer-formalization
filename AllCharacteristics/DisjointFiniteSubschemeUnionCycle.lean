import AllCharacteristics.DisjointFiniteSubschemeCycle
import AllCharacteristics.DisjointFiniteSubschemeUnion
import AllCharacteristics.FiniteSubschemeDatumDisjointUnion
import AllCharacteristics.FiniteSubschemeRank
import PfaffianDescent.FiniteSchemeFundamentalIso

/-!
# Cycles of affine disjoint finite unions

The product-coordinate presentation of a disjoint union carries precisely the
sum of the component fundamental cycles in the ambient scheme.  This records
scheme-theoretic local lengths, so it also applies to nonreduced summands.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u

private theorem pushforwardCycle_congr
    {U V : Scheme.{u}} (a b : U ⟶ V) [UniversallyClosed a] [UniversallyClosed b]
    (h : a = b) (z : EffectiveZeroCycle U) :
    pushforwardCycle a z = pushforwardCycle b z := by
  subst b
  rfl

/-- A datum and its canonical affine presentation carry the same ambient
fundamental cycle. -/
theorem finiteSubschemeDatumCycle_eq_pushforward_finiteSubschemeDatumSpecMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
    letI : IsFinite (finiteSubschemeDatumSpecMap f D ≫ f) := by
      haveI : IsAffine D.val.subscheme :=
        isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
      unfold finiteSubschemeDatumSpecMap
      rw [Category.assoc]
      infer_instance
    finiteSubschemeDatumCycle f D =
      pushforwardCycle (finiteSubschemeDatumSpecMap f D)
        (PfaffianDescent.finiteSchemeFundamentalCycle
          (finiteSubschemeDatumSpecMap f D ≫ f)) := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  haveI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  let e := D.val.subscheme.isoSpec
  letI : IsFinite (finiteSubschemeDatumSpecMap f D ≫ f) := by
    unfold finiteSubschemeDatumSpecMap
    rw [Category.assoc]
    infer_instance
  have hfund := PfaffianDescent.finiteSchemeFundamentalCycle_iso e.symm
    (finiteSubschemeDatumSpecMap f D ≫ f) (D.val.subschemeι ≫ f)
  change pushforwardCycle D.val.subschemeι
      (PfaffianDescent.finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f)) = _
  rw [← hfund, ← pushforwardCycle_comp]
  rfl

/-- The fundamental cycle carried by the product-coordinate presentation of
two disjoint affine finite subschemes is the sum of their ambient cycles. -/
theorem pushforwardCycle_disjointSpecUnionMap_finiteSchemeFundamentalCycle
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Module.Finite k A] [Module.Finite k B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hij : Disjoint (Set.range i) (Set.range j))
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B))) :
    let q := disjointSpecUnionMap i j
    letI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
    letI : IsFinite (i ≫ f) := by
      rw [hi]
      exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    letI : IsFinite (j ≫ f) := by
      rw [hj]
      exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    letI : IsFinite (q ≫ f) := by
      rw [disjointSpecUnionMap_toBase f i j hi hj]
      exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    pushforwardCycle q (PfaffianDescent.finiteSchemeFundamentalCycle (q ≫ f)) =
      pushforwardCycle i (PfaffianDescent.finiteSchemeFundamentalCycle (i ≫ f)) +
      pushforwardCycle j (PfaffianDescent.finiteSchemeFundamentalCycle (j ≫ f)) := by
  let q := disjointSpecUnionMap i j
  let c := coprod.desc i j
  let e := asIso (coprodSpec A B)
  letI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
  letI : IsClosedImmersion c := isClosedImmersion_coprodDesc_of_disjoint i j hij
  letI : IsClosedImmersion
      (coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B)) :=
    isClosedImmersion_coprod_inl
  letI : IsClosedImmersion
      (coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B)) :=
    isClosedImmersion_coprod_inr
  letI : IsFinite (i ≫ f) := by
    rw [hi]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite (j ≫ f) := by
    rw [hj]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite (q ≫ f) := by
    rw [show q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (A × B))) by
      exact disjointSpecUnionMap_toBase f i j hi hj]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hcbase : c ≫ f = coprod.desc (i ≫ f) (j ≫ f) := by
    apply coprod.hom_ext
    · simp [c]
    · simp [c]
  letI : IsFinite (c ≫ f) := by
    rw [hcbase]
    infer_instance
  have hq : q = e.inv ≫ c := by rfl
  have heq : e.hom ≫ q = c := by
    simp [hq]
  have hfund := PfaffianDescent.finiteSchemeFundamentalCycle_iso e (c ≫ f) (q ≫ f)
  change pushforwardCycle q (PfaffianDescent.finiteSchemeFundamentalCycle (q ≫ f)) = _
  rw [← hfund]
  rw [← pushforwardCycle_comp]
  have hqcycle : pushforwardCycle (e.hom ≫ q)
      (PfaffianDescent.finiteSchemeFundamentalCycle (c ≫ f)) =
      pushforwardCycle c (PfaffianDescent.finiteSchemeFundamentalCycle (c ≫ f)) := by
    simpa only [heq]
  rw [hqcycle]
  letI : IsArtinianScheme (Spec (.of A)) :=
    PfaffianDescent.finiteScheme_isArtinian (i ≫ f)
  letI : IsArtinianScheme (Spec (.of B)) :=
    PfaffianDescent.finiteScheme_isArtinian (j ≫ f)
  letI : IsArtinianScheme (Spec (.of A) ⨿ Spec (.of B)) :=
    PfaffianDescent.finiteScheme_isArtinian (c ≫ f)
  change pushforwardCycle c (fundamentalZeroCycle (Spec (.of A) ⨿ Spec (.of B))) = _
  rw [fundamentalZeroCycle_coprod_pushforward]
  rw [show pushforwardCycle c
      (pushforwardCycle (coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B))
          (fundamentalZeroCycle (Spec (.of A))) +
        pushforwardCycle (coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B))
          (fundamentalZeroCycle (Spec (.of B)))) =
      pushforwardCycle c
          (pushforwardCycle (coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B))
            (fundamentalZeroCycle (Spec (.of A)))) +
        pushforwardCycle c
          (pushforwardCycle (coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B))
            (fundamentalZeroCycle (Spec (.of B)))) by
      exact Finsupp.sum_add_index' (fun x => by simp)
        (fun x n m => by simp only [add_mul, Finsupp.single_add])]
  rw [show pushforwardCycle c
      (pushforwardCycle (coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B))
        (fundamentalZeroCycle (Spec (.of A)))) =
      pushforwardCycle ((coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B)) ≫ c)
        (fundamentalZeroCycle (Spec (.of A))) by
      exact (pushforwardCycle_comp _ _ _).symm]
  rw [show pushforwardCycle c
      (pushforwardCycle (coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B))
        (fundamentalZeroCycle (Spec (.of B)))) =
      pushforwardCycle ((coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B)) ≫ c)
        (fundamentalZeroCycle (Spec (.of B))) by
      exact (pushforwardCycle_comp _ _ _).symm]
  have hleft : (coprod.inl : Spec (.of A) ⟶ Spec (.of A) ⨿ Spec (.of B)) ≫ c = i := by
    dsimp [c]
    exact coprod.inl_desc _ _
  have hright : (coprod.inr : Spec (.of B) ⟶ Spec (.of A) ⨿ Spec (.of B)) ≫ c = j := by
    dsimp [c]
    exact coprod.inr_desc _ _
  rw [pushforwardCycle_congr _ _ hleft,
    pushforwardCycle_congr _ _ hright]
  rfl

/-- The canonical cycle of the finite-subscheme datum built from two disjoint
affine presentations is the sum of the component canonical ambient cycles. -/
theorem finiteSubschemeDatumCycle_disjointSpecUnion
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
    letI : IsFinite (i ≫ f) := by
      rw [hi]
      exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    letI : IsFinite (j ≫ f) := by
      rw [hj]
      exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    finiteSubschemeDatumCycle f
      (finiteSubschemeDatumOfDisjointSpecUnion f i j hi hj m n hmi hnj hij) =
      pushforwardCycle i (PfaffianDescent.finiteSchemeFundamentalCycle (i ≫ f)) +
      pushforwardCycle j (PfaffianDescent.finiteSchemeFundamentalCycle (j ≫ f)) := by
  let q := disjointSpecUnionMap i j
  letI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i j hij
  have hqbase : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (A × B))) :=
    disjointSpecUnionMap_toBase f i j hi hj
  letI : IsFinite (q ≫ f) := by
    rw [hqbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : Flat (q ≫ f) := by
    rw [hqbase]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  letI : Module.FinitePresentation k (A × B) :=
    Module.finitePresentation_of_finite k (A × B)
  letI : Algebra.FinitePresentation k (A × B) :=
    Algebra.FinitePresentation.of_finitePresentation k (A × B)
  letI : LocallyOfFinitePresentation (q ≫ f) := by
    rw [hqbase]
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hqrank : ∀ s : Spec (.of k), (q ≫ f).finrank s = m + n := fun s => by
    have hs : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst s
    exact finrank_disjointSpecUnionMap f i j hi hj m n hmi hnj
  change finiteSubschemeDatumCycle f
      (finiteSubschemeDatumOfClosedImmersion q f (m + n) hqrank) = _
  rw [finiteSubschemeDatumCycle_of_closedImmersion q f (m + n) hqrank]
  exact pushforwardCycle_disjointSpecUnionMap_finiteSchemeFundamentalCycle f i j hij hi hj

/-- The canonical cycle of two disjoint finite-subscheme data is the sum of
their canonical cycles. -/
theorem finiteSubschemeDatumCycleOfTwoDisjointData
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {m n : ℕ} (D₁ : FiniteSubschemeDatum f m) (D₂ : FiniteSubschemeDatum f n)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁))
      (Set.range (finiteSubschemeDatumSpecMap f D₂))) :
    finiteSubschemeDatumCycle f (finiteSubschemeDatumOfTwoDisjointData f D₁ D₂ h₁₂) =
      finiteSubschemeDatumCycle f D₁ + finiteSubschemeDatumCycle f D₂ := by
  letI : IsFinite (D₁.val.subschemeι ≫ f) := D₁.property.1
  letI : IsFinite (D₂.val.subschemeι ≫ f) := D₂.property.1
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₂.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₂.val.subschemeι ≫ f)
  let i₁ := finiteSubschemeDatumSpecMap f D₁
  let i₂ := finiteSubschemeDatumSpecMap f D₂
  letI : IsFinite (i₁ ≫ f) := by
    dsimp [i₁, finiteSubschemeDatumSpecMap]
    rw [Category.assoc]
    infer_instance
  letI : IsFinite (i₂ ≫ f) := by
    dsimp [i₂, finiteSubschemeDatumSpecMap]
    rw [Category.assoc]
    infer_instance
  have hi₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(D₁.val.subscheme, ⊤))) := by
    exact finiteSubschemeDatumSpecMap_toBase f D₁
  have hi₂ : i₂ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(D₂.val.subscheme, ⊤))) := by
    exact finiteSubschemeDatumSpecMap_toBase f D₂
  have hm : (i₁ ≫ f).finrank (IsLocalRing.closedPoint k) = m := by
    exact finiteSubschemeDatumSpecMap_finrank f D₁
  have hn : (i₂ ≫ f).finrank (IsLocalRing.closedPoint k) = n := by
    exact finiteSubschemeDatumSpecMap_finrank f D₂
  change finiteSubschemeDatumCycle f
      (finiteSubschemeDatumOfDisjointSpecUnion f i₁ i₂ hi₁ hi₂ m n hm hn h₁₂) = _
  rw [finiteSubschemeDatumCycle_disjointSpecUnion f i₁ i₂ hi₁ hi₂ m n hm hn h₁₂]
  rw [← finiteSubschemeDatumCycle_eq_pushforward_finiteSubschemeDatumSpecMap f D₁]
  rw [← finiteSubschemeDatumCycle_eq_pushforward_finiteSubschemeDatumSpecMap f D₂]

/-- The canonical cycle of three successively disjoint finite-subscheme data
is the sum of the three canonical cycles. -/
theorem finiteSubschemeDatumCycleOfThreeDisjointData
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {m n p : ℕ} (D₁ : FiniteSubschemeDatum f m)
    (D₂ : FiniteSubschemeDatum f n) (D₃ : FiniteSubschemeDatum f p)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁))
      (Set.range (finiteSubschemeDatumSpecMap f D₂)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap (finiteSubschemeDatumSpecMap f D₁)
        (finiteSubschemeDatumSpecMap f D₂)))
      (Set.range (finiteSubschemeDatumSpecMap f D₃))) :
    finiteSubschemeDatumCycle f
      (finiteSubschemeDatumOfThreeDisjointData f D₁ D₂ D₃ h₁₂ h₁₂₃) =
      finiteSubschemeDatumCycle f D₁ + finiteSubschemeDatumCycle f D₂ +
        finiteSubschemeDatumCycle f D₃ := by
  letI : IsFinite (D₁.val.subschemeι ≫ f) := D₁.property.1
  letI : IsFinite (D₂.val.subschemeι ≫ f) := D₂.property.1
  letI : IsFinite (D₃.val.subschemeι ≫ f) := D₃.property.1
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₂.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D₃.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₁.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₂.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficient_finite (D₃.val.subschemeι ≫ f)
  let i₁ := finiteSubschemeDatumSpecMap f D₁
  let i₂ := finiteSubschemeDatumSpecMap f D₂
  let i₃ := finiteSubschemeDatumSpecMap f D₃
  letI : IsFinite (i₁ ≫ f) := by
    dsimp [i₁, finiteSubschemeDatumSpecMap]
    rw [Category.assoc]
    infer_instance
  letI : IsFinite (i₂ ≫ f) := by
    dsimp [i₂, finiteSubschemeDatumSpecMap]
    rw [Category.assoc]
    infer_instance
  letI : IsFinite (i₃ ≫ f) := by
    dsimp [i₃, finiteSubschemeDatumSpecMap]
    rw [Category.assoc]
    infer_instance
  have hi₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(D₁.val.subscheme, ⊤))) := by
    exact finiteSubschemeDatumSpecMap_toBase f D₁
  have hi₂ : i₂ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(D₂.val.subscheme, ⊤))) := by
    exact finiteSubschemeDatumSpecMap_toBase f D₂
  have hi₃ : i₃ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(D₃.val.subscheme, ⊤))) := by
    exact finiteSubschemeDatumSpecMap_toBase f D₃
  have hm : (i₁ ≫ f).finrank (IsLocalRing.closedPoint k) = m := by
    exact finiteSubschemeDatumSpecMap_finrank f D₁
  have hn : (i₂ ≫ f).finrank (IsLocalRing.closedPoint k) = n := by
    exact finiteSubschemeDatumSpecMap_finrank f D₂
  have hp : (i₃ ≫ f).finrank (IsLocalRing.closedPoint k) = p := by
    exact finiteSubschemeDatumSpecMap_finrank f D₃
  let q := disjointSpecUnionMap i₁ i₂
  letI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i₁ i₂ h₁₂
  have hqbase : q ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap k (Γ(D₁.val.subscheme, ⊤) × Γ(D₂.val.subscheme, ⊤)))) :=
    disjointSpecUnionMap_toBase f i₁ i₂ hi₁ hi₂
  letI : IsFinite (q ≫ f) := by
    rw [hqbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hqrank : (q ≫ f).finrank (IsLocalRing.closedPoint k) = m + n :=
    finrank_disjointSpecUnionMap f i₁ i₂ hi₁ hi₂ m n hm hn
  change finiteSubschemeDatumCycle f
      (finiteSubschemeDatumOfDisjointSpecUnion f q i₃ hqbase hi₃ (m + n) p hqrank hp h₁₂₃) = _
  rw [finiteSubschemeDatumCycle_disjointSpecUnion f q i₃ hqbase hi₃ (m + n) p hqrank hp h₁₂₃]
  rw [pushforwardCycle_disjointSpecUnionMap_finiteSchemeFundamentalCycle f i₁ i₂ h₁₂ hi₁ hi₂]
  rw [← finiteSubschemeDatumCycle_eq_pushforward_finiteSubschemeDatumSpecMap f D₁]
  rw [← finiteSubschemeDatumCycle_eq_pushforward_finiteSubschemeDatumSpecMap f D₂]
  rw [← finiteSubschemeDatumCycle_eq_pushforward_finiteSubschemeDatumSpecMap f D₃]

/-- The degree-sixteen datum used to begin Voisin's reduction has canonical
cycle equal to its degree-ten component plus its two degree-three components. -/
theorem finiteSubschemeDatumCycle_rankSixteenOfDegreeTenAndTwoDegreeThree
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (D₁₀ : FiniteSubschemeDatum f 10)
    (D₃ : FiniteSubschemeDatum f 3) (D₃' : FiniteSubschemeDatum f 3)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap (finiteSubschemeDatumSpecMap f D₁₀)
        (finiteSubschemeDatumSpecMap f D₃)))
      (Set.range (finiteSubschemeDatumSpecMap f D₃'))) :
    finiteSubschemeDatumCycle f
      (finiteSubschemeDatum_rankSixteenOfDegreeTenAndTwoDegreeThree
        f D₁₀ D₃ D₃' h₁₂ h₁₂₃) =
      finiteSubschemeDatumCycle f D₁₀ + finiteSubschemeDatumCycle f D₃ +
        finiteSubschemeDatumCycle f D₃' := by
  simpa only [finiteSubschemeDatum_rankSixteenOfDegreeTenAndTwoDegreeThree]
    using finiteSubschemeDatumCycleOfThreeDisjointData f D₁₀ D₃ D₃' h₁₂ h₁₂₃

end AllCharacteristics
