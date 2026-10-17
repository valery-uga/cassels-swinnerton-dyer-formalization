import PfaffianDescent.GoodPairLineChartMaps
import PfaffianDescent.GrassmannianProper

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [CharZero K]

lemma goodMixedPairLine_overlap (ε δ : Fin 3 → Bool) (i : Fin 3) :
    pullback.fst (goodMixedPairToGlobalFiber K ε) (goodMixedPairToGlobalFiber K δ) ≫ goodMixedPairToLine K ε i =
      pullback.snd (goodMixedPairToGlobalFiber K ε) (goodMixedPairToGlobalFiber K δ) ≫ goodMixedPairToLine K δ i := by
  let F := goodMixedPairToGlobalFiber K ε
  let G := goodMixedPairToGlobalFiber K δ
  let Y := pullback F G
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (by norm_num)
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
end PfaffianDescent
