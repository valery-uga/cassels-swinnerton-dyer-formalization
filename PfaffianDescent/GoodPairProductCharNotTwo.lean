import PfaffianDescent.GoodPairProjProduct

/-! Characteristic-not-two scheme-theoretic first-two-form product.
The original goodPairIncidenceFiber, lineTripleScheme, projectiveLineProjTriple,
and all original scalar and chart maps are retained. Accepted CharZero
APIs remain untouched. Source candidate; acceptance is root-owned. -/


/- Generalized section from PfaffianDescent.GoodPairFieldCharts -/
namespace PfaffianDescent.CharNotTwo
open PfaffianDescent AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The first two isotropic forms' field-valued points are covered by all eight product charts. -/
theorem goodCommonPair_exists_standard_chart
    (W : Submodule K (Fin 3 → Fin 2 → K)) (hdim : finrank K W = 3)
    (h0 : ∀ x ∈ W, ∀ y ∈ W, goodSymplecticForm K x y = 0)
    (h1 : ∀ x ∈ W, ∀ y ∈ W,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0) :
    ∃ ε : Fin 3 → Bool, ∃ u : Fin 3 → K, W = goodBlockMixedGraph K ε u := by
  let L := goodBlockSubmodule K (Fin 2 → K) W
  have hL (i : Fin 3) : finrank K (L i) = 1 := goodCommonIsotropic_block_finrank W hdim h0 h1 i
  choose ε u hu using fun i => line_has_standard_chart (L i) (hL i)
  refine ⟨ε, u, ?_⟩
  ext x
  rw [mem_goodBlockMixedGraph]
  constructor
  · intro hx i
    exact (hu i (x i)).mp (goodBlockProjection_mem K (Fin 2 → K)
      (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K))) W (goodCommonIsotropic_invariant W hdim h0 h1) i hx)
  · intro hx
    rw [← goodBlockProjection_sum K (Fin 2 → K) x]
    exact W.sum_mem (fun i _ => (hu i (x i)).mpr (hx i))

end
end PfaffianDescent.CharNotTwo

/- Generalized section from PfaffianDescent.GoodPairMixedCoordinates -/
namespace PfaffianDescent.CharNotTwo
open PfaffianDescent AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Every ambient three-space isotropic for the first two forms belongs to one of the eight
specified charts of the actual Grassmannian atlas. -/
theorem goodAmbientPair_exists_graph
    (W : Submodule K ((Fin 3 → K) × (Fin 3 → K))) (hdim : finrank K W = 3)
    (hiso : ∀ k : Fin 2, alternatingRestriction K _ W (goodAmbientAlternatingForm K (k.castLE (by decide))) = 0) :
    ∃ ε : Fin 3 → Bool, ∃ u : Fin 3 → K,
      W.map (graphCoordinatePermutation K (goodMixedChartPermutation ε)).toLinearMap =
        (Matrix.toLin' (Matrix.diagonal u)).graph := by
  let e := goodAmbientBlockEquiv K
  let U := W.map e.toLinearMap
  have hdimU : finrank K U = 3 := (e.finrank_map_eq W).trans hdim
  have hval (k : Fin 2) (a : (Fin 3 → K) × (Fin 3 → K)) (ha : a ∈ W)
      (b : (Fin 3 → K) × (Fin 3 → K)) (hb : b ∈ W) :
      goodAmbientAlternatingForm K (k.castLE (by decide)) ![a, b] = 0 :=
    alternatingRestriction_pair_zero K W _ (hiso k) a ha b hb
  have h0 : ∀ x ∈ U, ∀ y ∈ U, goodSymplecticForm K x y = 0 := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have he : goodAmbientAlternatingForm K 0 ![a, b] = goodSymplecticForm K (e a) (e b) :=
      (goodAmbientAlternatingForm_pair K 0 a b).trans (goodTriple_zero_block_form K _ _)
    exact he.symm.trans (hval 0 a ha b hb)
  have h1 : ∀ x ∈ U, ∀ y ∈ U,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0 := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have he : goodAmbientAlternatingForm K 1 ![a, b] =
        goodSymplecticForm K (e a) (goodSpectralOperator K (Fin 2 → K) (e b)) :=
      (goodAmbientAlternatingForm_pair K 1 a b).trans (goodTriple_one_block_form K _ _)
    exact he.symm.trans (hval 1 a ha b hb)
  obtain ⟨ε, u, hu⟩ := goodCommonPair_exists_standard_chart U hdimU h0 h1
  refine ⟨ε, u, ?_⟩
  apply Submodule.map_injective_of_injective (goodSplitBlockCoordinates K).injective
  have he : (graphCoordinatePermutation K (goodMixedChartPermutation ε)).trans
      (goodSplitBlockCoordinates K) = e.trans (goodBlockCoordinateSwap K ε) := by
    apply LinearEquiv.ext
    exact goodMixedChartPermutation_coordinates K ε
  rw [← Submodule.map_comp]
  change W.map ((graphCoordinatePermutation K (goodMixedChartPermutation ε)).trans
    (goodSplitBlockCoordinates K)).toLinearMap = _
  rw [he]
  change W.map ((goodBlockCoordinateSwap K ε).toLinearMap.comp e.toLinearMap) = _
  rw [Submodule.map_comp]
  change U.map (goodBlockCoordinateSwap K ε).toLinearMap = _
  rw [hu, goodBlockMixedGraph_map_swap, goodSplitBlockCoordinates_diagonal_graph]

end
end PfaffianDescent.CharNotTwo

/- Generalized section from PfaffianDescent.GoodPairIncidenceOverlap -/

namespace PfaffianDescent.CharNotTwo
open PfaffianDescent
open Module
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Any field-valued incidence chart point over the good triple belongs to the
one of the eight product charts, irrespective of its initial chart label. -/
theorem goodPairIncidenceGraph_overlap
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints K)
    (hc : incidenceOriginalCoefficients i p = goodPairTripleSchemeCoefficients K) :
    ∃ ε : Fin 3 → Bool, Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation K (grassmannianChartChange i (goodMixedChartPermutation ε))) p.1) := by
  let e := graphCoordinatePermutation K i.symm
  let W := p.1.graph.map e.toLinearMap
  have hdim : finrank K W = 3 := by
    calc
      finrank K W = finrank K p.1.graph := e.finrank_map_eq _
      _ = finrank K (Fin 3 → K) := (graphSourceEquiv K p.1).finrank_eq
      _ = 3 := Module.finrank_fin_fun K
  have hforms (k : Fin 3) : incidenceOriginalForm i p k = goodPairAmbientAlternatingForm K k := by
    apply (alternatingCoordinates (incidenceAmbientBasis K)).injective
    funext s
    exact congrFun hc (k, s)
  have hiso (k : Fin 2) : alternatingRestriction K _ W
      (goodAmbientAlternatingForm K (k.castLE (by decide))) = 0 := by
    have hne : k.castLE (by decide : 2 ≤ 3) ≠ (2 : Fin 3) := by
      intro h
      have hv := congrArg Fin.val h
      have hk := k.isLt
      simp only [Fin.val_castLE, Fin.val_ofNat] at hv
      omega
    have hb : incidenceOriginalForm i p (k.castLE (by decide)) =
        goodAmbientAlternatingForm K (k.castLE (by decide)) :=
      (hforms _).trans (if_neg hne)
    exact congrArg (alternatingRestriction K _ W) hb |>.symm.trans
      (alternatingTransport_isotropic e p.1.graph W rfl (p.2 _).1 (p.2 _).2)
  obtain ⟨ε, u, hu⟩ := goodAmbientPair_exists_graph W hdim hiso
  refine ⟨ε, ?_⟩
  have he : p.1.graph.map
      (graphCoordinatePermutation K (grassmannianChartChange i (goodMixedChartPermutation ε))).toLinearMap =
      W.map (graphCoordinatePermutation K (goodMixedChartPermutation ε)).toLinearMap := by
    change p.1.graph.map (graphCoordinatePermutation K (grassmannianChartChange i (goodMixedChartPermutation ε))).toLinearMap =
      (p.1.graph.map (graphCoordinatePermutation K i.symm).toLinearMap).map
        (graphCoordinatePermutation K (goodMixedChartPermutation ε)).toLinearMap
    rw [← Submodule.map_comp]
    change p.1.graph.map (graphCoordinatePermutation K (grassmannianChartChange i (goodMixedChartPermutation ε))).toLinearMap =
      p.1.graph.map ((graphCoordinatePermutation K i.symm).trans
        (graphCoordinatePermutation K (goodMixedChartPermutation ε))).toLinearMap
    rw [graphCoordinatePermutation_trans]
    rfl
  apply (graphTransition_overlap_iff _ _).mpr
  rw [he, hu]
  exact graphChartQuotientMap_graph_bijective _

end
end PfaffianDescent.CharNotTwo

/- Generalized section from PfaffianDescent.GoodPairIncidenceFieldPoints -/
namespace PfaffianDescent.CharNotTwo
open PfaffianDescent AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)] {L : Type u} [Field L] [Algebra K L]

/-- Every field-valued point of the global incidence over the first two forms factors
through one of the eight specified charts. This applies to all residue fields of the fiber. -/
theorem goodPairIncidence_field_factor (f : Spec (.of L) ⟶ incidenceScheme K)
    (h : f ≫ incidenceToTriples K =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ goodPairTripleSection K) :
    ∃ ε : Fin 3 → Bool, ∃ g : Spec (.of L) ⟶ incidenceGraphScheme K,
      g ≫ incidenceChartι K (goodMixedChartPermutation ε) = f := by
  letI : NeZero (2 : L) := ⟨by
    intro htwo
    apply NeZero.ne (2 : K)
    apply (algebraMap K L).injective
    simpa only [map_ofNat, map_zero] using htwo⟩
  have hf : f ≫ incidenceToBase K = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    have he := congrArg (fun t => t ≫ alternatingTripleToBase K) h
    simpa only [Category.assoc, incidenceToTriples_toBase,
      goodPairTripleSection_toBase, Category.comp_id] using he
  obtain ⟨i, p, hp⟩ := incidence_local_algebra_point K f hf
  have ht : incidenceChartEvaluation K p ≫ incidenceChartToTriples K i =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ goodPairTripleSection K := by
    calc
      incidenceChartEvaluation K p ≫ incidenceChartToTriples K i =
          incidenceChartEvaluation K p ≫ (incidenceChartι K i ≫ incidenceToTriples K) :=
        congrArg (fun t => incidenceChartEvaluation K p ≫ t) (incidenceChartι_toTriples K i).symm
      _ = (incidenceChartEvaluation K p ≫ incidenceChartι K i) ≫ incidenceToTriples K :=
        (Category.assoc _ _ _).symm
      _ = f ≫ incidenceToTriples K := congrArg (fun t => t ≫ incidenceToTriples K) hp
      _ = _ := h
  have hc := incidenceChartEvaluation_goodPair_coefficients K i p ht
  obtain ⟨ε, hε⟩ := goodPairIncidenceGraph_overlap i p hc
  obtain ⟨g, hg⟩ := incidenceChartEvaluation_rechart K i (goodMixedChartPermutation ε) p hε
  exact ⟨ε, g, hg.trans hp⟩

end
end PfaffianDescent.CharNotTwo

/- Generalized section from PfaffianDescent.GoodPairIncidenceAtlas -/

namespace PfaffianDescent.CharNotTwo
open PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The eight actual affine charts cover every point of the full first-two-form fiber. -/
theorem goodMixedPairCharts_cover (x : goodPairIncidenceFiber K) :
    ∃ ε : Fin 3 → Bool, ∃ y : goodMixedPairScheme K, goodMixedPairToGlobalFiber K ε y = x := by
  let L : Type u := (goodPairIncidenceFiber K).residueField x
  let z : Spec (.of L) ⟶ goodPairIncidenceFiber K := (goodPairIncidenceFiber K).fromSpecResidueField x
  let ψ : K →+* L := (Spec.preimage (z ≫ goodPairIncidenceFiberToBase K)).hom
  letI : Algebra K L := ψ.toAlgebra
  have hz : Spec.map (CommRingCat.ofHom (algebraMap K L)) = z ≫ goodPairIncidenceFiberToBase K :=
    Spec.map_preimage _
  let f : Spec (.of L) ⟶ incidenceScheme K :=
    z ≫ pullback.fst (incidenceToTriples K) (goodPairTripleSection K)
  have ht : f ≫ incidenceToTriples K =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ goodPairTripleSection K := by
    calc
      f ≫ incidenceToTriples K = z ≫
          (pullback.fst (incidenceToTriples K) (goodPairTripleSection K) ≫ incidenceToTriples K) :=
        Category.assoc _ _ _
      _ = z ≫ (goodPairIncidenceFiberToBase K ≫ goodPairTripleSection K) :=
        congrArg (fun t => z ≫ t) pullback.condition
      _ = (z ≫ goodPairIncidenceFiberToBase K) ≫ goodPairTripleSection K := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun t => t ≫ goodPairTripleSection K) hz.symm
  obtain ⟨ε, g, hg⟩ := goodPairIncidence_field_factor K f ht
  let hP := goodMixedPair_global_chart_isPullback K
    (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K))) ε
  let q : Spec (.of L) ⟶ goodMixedPairScheme K := hP.lift z g hg.symm
  refine ⟨ε, q (IsLocalRing.closedPoint L), ?_⟩
  have hq : q ≫ goodMixedPairToGlobalFiber K ε = z := hP.lift_fst z g hg.symm
  exact (congrArg (fun t : Spec (.of L) ⟶ goodPairIncidenceFiber K => t (IsLocalRing.closedPoint L)) hq).trans
    ((goodPairIncidenceFiber K).fromSpecResidueField_apply x (IsLocalRing.closedPoint L))

/-- The complete eight-chart affine atlas of the scheme-theoretic first-two-form locus. -/
noncomputable def goodPairIncidenceOpenCover : Scheme.OpenCover.{u} (goodPairIncidenceFiber K) where
  I₀ := ULift.{u} (Fin 3 → Bool)
  X _ := goodMixedPairScheme K
  f ε := goodMixedPairToGlobalFiber K ε.down
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨ε, y, hy⟩ := goodMixedPairCharts_cover K x
      exact ⟨⟨ε⟩, y, hy⟩
    · intro ε
      exact goodMixedPairToGlobalFiber_open K
        (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K))) ε.down

lemma goodMixedPairToBase_relativeDimension : SmoothOfRelativeDimension 3 (goodMixedPairToBase K) := by
  change SmoothOfRelativeDimension 3
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K))))
  simpa only [Nat.card_fin] using polynomial_smooth_relative_dimension K (Fin 3)

instance goodPairIncidenceFiberToBase_relativeDimension :
    SmoothOfRelativeDimension 3 (goodPairIncidenceFiberToBase K) := by
  let 𝒰 := goodPairIncidenceOpenCover K
  letI (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin 3) K))))
  apply HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension 3) 𝒰
  intro i
  have hs : SmoothOfRelativeDimension 3 (𝒰.f i ≫ goodPairIncidenceFiberToBase K) := by
    change SmoothOfRelativeDimension 3 (goodMixedPairToGlobalFiber K i.down ≫ goodPairIncidenceFiberToBase K)
    rw [goodMixedPairToGlobalFiber_toBase]
    exact goodMixedPairToBase_relativeDimension K
  exact HasRingHomProperty.appTop _ _ hs

/-- The full first-two-form locus is a smooth three-dimensional proper scheme. -/
theorem goodPairIncidenceFiber_dimension : topologicalKrullDim (goodPairIncidenceFiber K) = 3 := by
  apply scheme_dimension_eq_of_openCover (goodPairIncidenceOpenCover K) ⟨fun _ => false⟩
  intro i
  change topologicalKrullDim (Spec (.of (MvPolynomial (Fin 3) K))) = 3
  rw [polynomialSpec_dimension, Nat.card_fin]
  norm_num

end
end PfaffianDescent.CharNotTwo

/- Generalized section from PfaffianDescent.GoodPairLineProjections -/

namespace PfaffianDescent.CharNotTwo
open PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

lemma goodMixedPairLine_overlap (ε δ : Fin 3 → Bool) (i : Fin 3) :
    pullback.fst (goodMixedPairToGlobalFiber K ε) (goodMixedPairToGlobalFiber K δ) ≫ goodMixedPairToLine K ε i =
      pullback.snd (goodMixedPairToGlobalFiber K ε) (goodMixedPairToGlobalFiber K δ) ≫ goodMixedPairToLine K δ i := by
  let F := goodMixedPairToGlobalFiber K ε
  let G := goodMixedPairToGlobalFiber K δ
  let Y := pullback F G
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K))
  haveI : IsOpenImmersion F := goodMixedPairToGlobalFiber_open K h2 ε
  haveI : IsOpenImmersion G := goodMixedPairToGlobalFiber_open K h2 δ
  haveI : AlgebraicGeometry.IsReduced (goodMixedPairScheme K) :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of (MvPolynomial (Fin 3) K))))
  haveI : AlgebraicGeometry.IsReduced Y := isReduced_of_isOpenImmersion (pullback.fst F G)
  have hb : pullback.fst F G ≫ goodMixedPairToBase K = pullback.snd F G ≫ goodMixedPairToBase K := by
    have he := congrArg (fun f => f ≫ goodPairIncidenceFiberToBase K) (pullback.condition (f := F) (g := G))
    have hF : F ≫ goodPairIncidenceFiberToBase K = goodMixedPairToBase K := goodMixedPairToGlobalFiber_toBase K ε
    have hG : G ≫ goodPairIncidenceFiberToBase K = goodMixedPairToBase K := goodMixedPairToGlobalFiber_toBase K δ
    simpa only [Category.assoc, hF, hG] using he
  apply ext_of_fromSpecResidueField_eq _ _ (grassmannianToBase K 1 1) Set.univ (by simp)
  · intro x hx
    let L : Type u := Y.residueField x
    let z : Spec (.of L) ⟶ Y := Y.fromSpecResidueField x
    let f : Spec (.of L) ⟶ goodMixedPairScheme K := z ≫ pullback.fst F G
    let g : Spec (.of L) ⟶ goodMixedPairScheme K := z ≫ pullback.snd F G
    let ψ : K →+* L := (Spec.preimage (f ≫ goodMixedPairToBase K)).hom
    letI : Algebra K L := ψ.toAlgebra
    have hf : f ≫ goodMixedPairToBase K = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
      (Spec.map_preimage _).symm
    have he : f ≫ goodMixedPairToBase K = g ≫ goodMixedPairToBase K := by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => z ≫ q) hb).trans (Category.assoc _ _ _).symm)
    have hg : g ≫ goodMixedPairToBase K = Spec.map (CommRingCat.ofHom (algebraMap K L)) := he.symm.trans hf
    obtain ⟨u, hu⟩ := polynomialSchemeEvaluation_exists K (Fin 3) f hf
    obtain ⟨v, hv⟩ := polynomialSchemeEvaluation_exists K (Fin 3) g hg
    have hfg : f ≫ F = g ≫ G :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => z ≫ q) (pullback.condition (f := F) (g := G))).trans (Category.assoc _ _ _).symm)
    have huv : polynomialSchemeEvaluation K (Fin 3) u ≫ goodMixedPairToGlobalFiber K ε =
        polynomialSchemeEvaluation K (Fin 3) v ≫ goodMixedPairToGlobalFiber K δ := by
      rw [hu, hv]
      exact hfg
    have hl := goodMixedPairEvaluation_line_eq K ε δ u v huv i
    rw [hu, hv] at hl
    exact (Category.assoc _ _ _).symm.trans (hl.trans (Category.assoc _ _ _))
  · simpa only [Category.assoc, goodMixedPairToLine_toBase] using hb

/-- The actual global line projection from the pair-isotropic locus to the `i`-th projective line. -/
noncomputable def goodPairToLine (i : Fin 3) : goodPairIncidenceFiber K ⟶ grassmannianScheme K 1 1 :=
  (goodPairIncidenceOpenCover K).glueMorphisms
    (fun ε => goodMixedPairToLine K ε.down i)
    (fun ε δ => goodMixedPairLine_overlap K ε.down δ.down i)

lemma goodMixedPairToGlobalFiber_toLine (ε : Fin 3 → Bool) (i : Fin 3) :
    goodMixedPairToGlobalFiber K ε ≫ goodPairToLine K i = goodMixedPairToLine K ε i :=
  (goodPairIncidenceOpenCover K).ι_glueMorphisms
    (fun ε => goodMixedPairToLine K ε.down i)
    (fun ε δ => goodMixedPairLine_overlap K ε.down δ.down i) ⟨ε⟩

lemma goodPairToLine_toBase (i : Fin 3) :
    goodPairToLine K i ≫ grassmannianToBase K 1 1 = goodPairIncidenceFiberToBase K := by
  apply (goodPairIncidenceOpenCover K).hom_ext
  intro ε
  change goodMixedPairToGlobalFiber K ε.down ≫ (goodPairToLine K i ≫ grassmannianToBase K 1 1) =
    goodMixedPairToGlobalFiber K ε.down ≫ goodPairIncidenceFiberToBase K
  rw [← Category.assoc, goodMixedPairToGlobalFiber_toLine, goodMixedPairToLine_toBase,
    goodMixedPairToGlobalFiber_toBase]

end
end PfaffianDescent.CharNotTwo

/- Generalized section from PfaffianDescent.TripleLineScheme -/
namespace PfaffianDescent.CharNotTwo
open PfaffianDescent AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The global comparison map from the actual pair-isotropic scheme to the product of three lines. -/
noncomputable def goodPairToLineTriple : goodPairIncidenceFiber K ⟶ lineTripleScheme K :=
  lineTripleLift K (goodPairIncidenceFiberToBase K) (goodPairToLine K) (goodPairToLine_toBase K)

lemma goodPairToLineTriple_projection (i : Fin 3) :
    goodPairToLineTriple K ≫ lineTripleProjection K i = goodPairToLine K i :=
  lineTripleLift_projection K _ _ _ i

lemma goodPairToLineTriple_toBase :
    goodPairToLineTriple K ≫ lineTripleToBase K = goodPairIncidenceFiberToBase K := by
  change goodPairToLineTriple K ≫ (lineTripleProjection K 0 ≫ grassmannianToBase K 1 1) = _
  rw [← Category.assoc, goodPairToLineTriple_projection, goodPairToLine_toBase]

lemma goodPairToLineTriple_onChart (ε : Fin 3 → Bool) :
    goodMixedPairToGlobalFiber K ε ≫ goodPairToLineTriple K = lineTripleChartMap K ε := by
  apply lineTriple_hom_ext K
  intro i
  rw [Category.assoc, goodPairToLineTriple_projection, goodMixedPairToGlobalFiber_toLine,
    lineTripleChartMap_projection]

end
end PfaffianDescent.CharNotTwo

/- Generalized section from PfaffianDescent.GoodPairProductIsomorphism -/

namespace PfaffianDescent.CharNotTwo
open PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

lemma lineTripleIncidence_overlap (ε δ : Fin 3 → Bool) :
    pullback.fst (lineTripleChartMap K ε) (lineTripleChartMap K δ) ≫ goodMixedPairToGlobalFiber K ε =
      pullback.snd (lineTripleChartMap K ε) (lineTripleChartMap K δ) ≫ goodMixedPairToGlobalFiber K δ := by
  let F := lineTripleChartMap K ε
  let G := lineTripleChartMap K δ
  let Y := pullback F G
  haveI : IsOpenImmersion F := lineTripleChartMap_open K ε
  haveI : IsOpenImmersion G := lineTripleChartMap_open K δ
  haveI : AlgebraicGeometry.IsReduced (goodMixedPairScheme K) :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of (MvPolynomial (Fin 3) K))))
  haveI : AlgebraicGeometry.IsReduced Y := isReduced_of_isOpenImmersion (pullback.fst F G)
  have hb : pullback.fst F G ≫ goodMixedPairToBase K = pullback.snd F G ≫ goodMixedPairToBase K := by
    have he := congrArg (fun f => f ≫ lineTripleToBase K) (pullback.condition (f := F) (g := G))
    have hF : F ≫ lineTripleToBase K = goodMixedPairToBase K := lineTripleChartMap_toBase K ε
    have hG : G ≫ lineTripleToBase K = goodMixedPairToBase K := lineTripleChartMap_toBase K δ
    simpa only [Category.assoc, hF, hG] using he
  apply ext_of_fromSpecResidueField_eq _ _ (goodPairIncidenceFiberToBase K) Set.univ (by simp)
  · intro x hx
    let L : Type u := Y.residueField x
    let z : Spec (.of L) ⟶ Y := Y.fromSpecResidueField x
    let f : Spec (.of L) ⟶ goodMixedPairScheme K := z ≫ pullback.fst F G
    let g : Spec (.of L) ⟶ goodMixedPairScheme K := z ≫ pullback.snd F G
    let ψ : K →+* L := (Spec.preimage (f ≫ goodMixedPairToBase K)).hom
    letI : Algebra K L := ψ.toAlgebra
    have hf : f ≫ goodMixedPairToBase K = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
      (Spec.map_preimage _).symm
    have he : f ≫ goodMixedPairToBase K = g ≫ goodMixedPairToBase K := by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => z ≫ q) hb).trans (Category.assoc _ _ _).symm)
    have hg : g ≫ goodMixedPairToBase K = Spec.map (CommRingCat.ofHom (algebraMap K L)) := he.symm.trans hf
    obtain ⟨u, hu⟩ := polynomialSchemeEvaluation_exists K (Fin 3) f hf
    obtain ⟨v, hv⟩ := polynomialSchemeEvaluation_exists K (Fin 3) g hg
    have hfg : f ≫ F = g ≫ G :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => z ≫ q) (pullback.condition (f := F) (g := G))).trans (Category.assoc _ _ _).symm)
    have hl (i : Fin 3) : polynomialSchemeEvaluation K (Fin 3) u ≫ goodMixedPairToLine K ε i =
        polynomialSchemeEvaluation K (Fin 3) v ≫ goodMixedPairToLine K δ i := by
      rw [hu, hv]
      have hF : F ≫ lineTripleProjection K i = goodMixedPairToLine K ε i := lineTripleChartMap_projection K ε i
      have hG : G ≫ lineTripleProjection K i = goodMixedPairToLine K δ i := lineTripleChartMap_projection K δ i
      have hp := congrArg (fun q => q ≫ lineTripleProjection K i) hfg
      have hp' : f ≫ goodMixedPairToLine K ε i = g ≫ goodMixedPairToLine K δ i := by
        simpa only [Category.assoc, hF, hG] using hp
      exact hp' 
    have hp := goodMixedPairEvaluation_eq_of_lines K ε δ u v hl
    rw [hu, hv] at hp
    exact (Category.assoc _ _ _).symm.trans (hp.trans (Category.assoc _ _ _))
  · simpa only [Category.assoc, goodMixedPairToGlobalFiber_toBase] using hb

/-- The direct sum of the three line factors, as a global morphism of schemes. -/
noncomputable def lineTripleToGoodPair : lineTripleScheme K ⟶ goodPairIncidenceFiber K :=
  (lineTripleOpenCover K).glueMorphisms
    (fun ε => goodMixedPairToGlobalFiber K ε.down)
    (fun ε δ => lineTripleIncidence_overlap K ε.down δ.down)

lemma lineTripleChartMap_toGoodPair (ε : Fin 3 → Bool) :
    lineTripleChartMap K ε ≫ lineTripleToGoodPair K = goodMixedPairToGlobalFiber K ε :=
  (lineTripleOpenCover K).ι_glueMorphisms
    (fun ε => goodMixedPairToGlobalFiber K ε.down)
    (fun ε δ => lineTripleIncidence_overlap K ε.down δ.down) ⟨ε⟩

lemma goodPairToLineTriple_comp_inverse : goodPairToLineTriple K ≫ lineTripleToGoodPair K = 𝟙 _ := by
  apply (goodPairIncidenceOpenCover K).hom_ext
  intro ε
  change goodMixedPairToGlobalFiber K ε.down ≫ (goodPairToLineTriple K ≫ lineTripleToGoodPair K) =
    goodMixedPairToGlobalFiber K ε.down ≫ 𝟙 _
  rw [← Category.assoc, goodPairToLineTriple_onChart, lineTripleChartMap_toGoodPair, Category.comp_id]

lemma lineTripleToGoodPair_comp_inverse : lineTripleToGoodPair K ≫ goodPairToLineTriple K = 𝟙 _ := by
  apply (lineTripleOpenCover K).hom_ext
  intro ε
  change lineTripleChartMap K ε.down ≫ (lineTripleToGoodPair K ≫ goodPairToLineTriple K) =
    lineTripleChartMap K ε.down ≫ 𝟙 _
  rw [← Category.assoc, lineTripleChartMap_toGoodPair, goodPairToLineTriple_onChart, Category.comp_id]

/-- The complete scheme-theoretic first-two-form locus is the product of the three projective lines. -/
noncomputable def goodPairProductIso : goodPairIncidenceFiber K ≅ lineTripleScheme K where
  hom := goodPairToLineTriple K
  inv := lineTripleToGoodPair K
  hom_inv_id := goodPairToLineTriple_comp_inverse K
  inv_hom_id := lineTripleToGoodPair_comp_inverse K

lemma goodPairProductIso_overBase :
    (goodPairProductIso K).hom ≫ lineTripleToBase K = goodPairIncidenceFiberToBase K :=
  goodPairToLineTriple_toBase K

lemma goodPairProductIso_projection (i : Fin 3) :
    (goodPairProductIso K).hom ≫ lineTripleProjection K i = goodPairToLine K i :=
  goodPairToLineTriple_projection K i

end
end PfaffianDescent.CharNotTwo

/- Generalized section from PfaffianDescent.GoodPairProjProduct -/
namespace PfaffianDescent.CharNotTwo
open PfaffianDescent AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The full first-two-form isotropic locus is the product of three standard Proj projective lines. -/
noncomputable def goodPairProjProductIso : goodPairIncidenceFiber K ≅ projectiveLineProjTriple K :=
  goodPairProductIso K ≪≫ lineTripleProjIso K

lemma goodPairProjProductIso_toBase :
    (goodPairProjProductIso K).hom ≫ projectiveLineProjTripleToBase K = goodPairIncidenceFiberToBase K := by
  change ((goodPairProductIso K).hom ≫ (lineTripleProjIso K).hom) ≫ projectiveLineProjTripleToBase K = _
  rw [Category.assoc, lineTripleProjIso_toBase]
  exact goodPairProductIso_overBase K

end
end PfaffianDescent.CharNotTwo
