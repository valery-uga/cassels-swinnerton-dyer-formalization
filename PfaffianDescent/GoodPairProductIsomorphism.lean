import PfaffianDescent.TripleLineCoordinates
import PfaffianDescent.GoodPairFiberExt

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [CharZero K]

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
end PfaffianDescent
