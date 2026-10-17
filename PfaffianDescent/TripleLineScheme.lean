import PfaffianDescent.ProjectiveLineAtlas
import PfaffianDescent.GoodPairLineProjections

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

/-- The product of two projective-line schemes over the coefficient base. -/
noncomputable abbrev linePairScheme : Scheme.{u} :=
  pullback (grassmannianToBase K 1 1) (grassmannianToBase K 1 1)

noncomputable def linePairToBase : linePairScheme K ⟶ Spec (.of K) :=
  pullback.fst _ _ ≫ grassmannianToBase K 1 1

/-- The actual iterated fiber product of three projective-line schemes. -/
noncomputable abbrev lineTripleScheme : Scheme.{u} :=
  pullback (grassmannianToBase K 1 1) (linePairToBase K)

noncomputable def lineTripleProjection (i : Fin 3) : lineTripleScheme K ⟶ grassmannianScheme K 1 1 :=
  ![pullback.fst _ _,
    pullback.snd _ _ ≫ pullback.fst _ _,
    pullback.snd _ _ ≫ pullback.snd _ _] i

noncomputable def lineTripleToBase : lineTripleScheme K ⟶ Spec (.of K) :=
  pullback.fst _ _ ≫ grassmannianToBase K 1 1

lemma lineTripleProjection_toBase (i : Fin 3) :
    lineTripleProjection K i ≫ grassmannianToBase K 1 1 = lineTripleToBase K := by
  fin_cases i
  · rfl
  · exact (Category.assoc _ _ _).trans (pullback.condition.symm)
  · change (pullback.snd (grassmannianToBase K 1 1) (linePairToBase K) ≫
      pullback.snd (grassmannianToBase K 1 1) (grassmannianToBase K 1 1)) ≫ _ = _
    rw [Category.assoc, ← pullback.condition]
    exact pullback.condition.symm

noncomputable def lineTripleLift {X : Scheme.{u}} (b : X ⟶ Spec (.of K))
    (f : Fin 3 → (X ⟶ grassmannianScheme K 1 1))
    (hf : ∀ i, f i ≫ grassmannianToBase K 1 1 = b) : X ⟶ lineTripleScheme K :=
  pullback.lift (f 0) (pullback.lift (f 1) (f 2) ((hf 1).trans (hf 2).symm)) (by
    change f 0 ≫ grassmannianToBase K 1 1 =
      pullback.lift (f 1) (f 2) ((hf 1).trans (hf 2).symm) ≫
        (pullback.fst _ _ ≫ grassmannianToBase K 1 1)
    rw [← Category.assoc, pullback.lift_fst, hf 0, hf 1])

lemma lineTripleLift_projection {X : Scheme.{u}} (b : X ⟶ Spec (.of K))
    (f : Fin 3 → (X ⟶ grassmannianScheme K 1 1))
    (hf : ∀ i, f i ≫ grassmannianToBase K 1 1 = b) (i : Fin 3) :
    lineTripleLift K b f hf ≫ lineTripleProjection K i = f i := by
  fin_cases i
  · exact pullback.lift_fst _ _ _
  · change lineTripleLift K b f hf ≫
      (pullback.snd (grassmannianToBase K 1 1) (linePairToBase K) ≫
        pullback.fst (grassmannianToBase K 1 1) (grassmannianToBase K 1 1)) = f 1
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ pullback.fst (grassmannianToBase K 1 1)
        (grassmannianToBase K 1 1)) (pullback.lift_snd _ _ _)).trans
          (pullback.lift_fst _ _ _))
  · change lineTripleLift K b f hf ≫
      (pullback.snd (grassmannianToBase K 1 1) (linePairToBase K) ≫
        pullback.snd (grassmannianToBase K 1 1) (grassmannianToBase K 1 1)) = f 2
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ pullback.snd (grassmannianToBase K 1 1)
        (grassmannianToBase K 1 1)) (pullback.lift_snd _ _ _)).trans
          (pullback.lift_snd _ _ _))

lemma lineTriple_hom_ext {X : Scheme.{u}} (f g : X ⟶ lineTripleScheme K)
    (h : ∀ i, f ≫ lineTripleProjection K i = g ≫ lineTripleProjection K i) : f = g := by
  apply pullback.hom_ext
  · exact h 0
  · apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((h 1).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((h 2).trans (Category.assoc _ _ _).symm)

/-- The product chart determined by three coordinate choices and three affine slopes. -/
noncomputable def lineTripleChartMap (ε : Fin 3 → Bool) : goodMixedPairScheme K ⟶ lineTripleScheme K :=
  lineTripleLift K (goodMixedPairToBase K) (goodMixedPairToLine K ε) (goodMixedPairToLine_toBase K ε)

lemma lineTripleChartMap_projection (ε : Fin 3 → Bool) (i : Fin 3) :
    lineTripleChartMap K ε ≫ lineTripleProjection K i = goodMixedPairToLine K ε i :=
  lineTripleLift_projection K _ _ _ i

lemma lineTripleChartMap_toBase (ε : Fin 3 → Bool) :
    lineTripleChartMap K ε ≫ lineTripleToBase K = goodMixedPairToBase K := by
  change lineTripleChartMap K ε ≫ (lineTripleProjection K 0 ≫ grassmannianToBase K 1 1) = _
  rw [← Category.assoc, lineTripleChartMap_projection, goodMixedPairToLine_toBase]

end
section
variable (K : Type u) [Field K] [CharZero K]

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
end PfaffianDescent
