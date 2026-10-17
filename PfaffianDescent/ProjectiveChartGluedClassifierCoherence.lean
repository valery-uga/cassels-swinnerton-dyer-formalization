import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSchemeGlueData
import PfaffianDescent.ProjectiveChartUniversalWholeFamilyOverlap

/-! Two actual local classifier maps with the same WHOLE ambient family
give the same map into the constructed global scheme. The actual overlap
factor and transition relation are derived. This is a comparison lemma
for the forward classifier and inverse injectivity, not a supplied matching
premise in the eventual original global representability caller. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false

variable {J : Type u} {X B : Scheme.{u}} (F : X ⟶ B) (U : J → X.Opens) (n : ℕ)
variable [IsSeparated F] (H : J → Over B)
variable (eta : ∀ i, relativeFiniteFlatHilbertFunctor197 ((U i).ι ≫ F) n ≅ yoneda.obj (H i))

/-- Whole-family equality of two original local classifier maps forces
their SAME global map. Landing in the actual overlap and the transition
relation are CONSTRUCTED from the existing whole-family criterion. -/
theorem relativeOpenChartParameterGluedClassifier_eq_of_sameWholeFamily001
    (i j : J) (T : Over B) (g : T ⟶ H i) (h : T ⟶ H j)
    (hFamily : relativeOpenChartClassifiedAmbientPoint001 F (U i) n (H i) (eta i) T g =
      relativeOpenChartClassifiedAmbientPoint001 F (U j) n (H j) (eta j) T h) :
    g ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i =
      h ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j := by
  let W := relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)
  have hLanding : Set.range g.left ⊆ (W : Set (H i).left) := by
    apply (relativeOpenChartParameterOverlap_range_iff_entireFamily001 F (U i) (U j) n
      (H i) (eta i) T g).mpr
    rw [hFamily]
    exact relativeOpenChartClassifiedAmbientPoint_entireSource_in_ownChart001 F (U j) n
      (H j) (eta j) T h
  have hRange : Set.range g.left ⊆ Set.range W.ι := by
    simpa only [W.range_ι] using hLanding
  let r := IsOpenImmersion.lift W.ι g.left hRange
  let k : T ⟶ relativeOpenChartParameterOverlapTest001 F (U i) (U j) n (H i) (eta i) := by
    refine Over.homMk r ?_
    change r ≫ (W.ι ≫ (H i).hom) = T.hom
    exact (Category.assoc r W.ι (H i).hom).symm.trans
      ((congrArg (fun f => f ≫ (H i).hom) (IsOpenImmersion.lift_fac W.ι g.left hRange)).trans
        (Over.w g))
  have hKi : k ≫ relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n
      (H i) (eta i) = g := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac W.ι g.left hRange
  have hKt : k ≫ relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
      (H i) (H j) (eta i) (eta j) = h := by
    apply relativeOpenChartClassifiedAmbientPoint_injective001 F (U j) n (H j) (eta j) T
    let P0 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
      relativeOpenChartClassifiedAmbientPoint001 F (U j) n (H j) (eta j) T
        (k ≫ relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
          (H i) (H j) (eta i) (eta j))
    let P1 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map
        (k ≫ relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
          (H i) (H j) (eta i) (eta j)).op
        (relativeOpenChartUniversalAmbientPoint001 F (U j) n (H j) (eta j))
    let P2 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map
        (k ≫ relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n
          (H i) (eta i)).op
        (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i))
    let P3 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map g.op
        (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i))
    let P4 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
      relativeOpenChartClassifiedAmbientPoint001 F (U i) n (H i) (eta i) T g
    let P5 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
      relativeOpenChartClassifiedAmbientPoint001 F (U j) n (H j) (eta j) T h
    have h01 : P0 = P1 := relativeOpenChartClassifiedAmbientPoint_eq_pullback001
      F (U j) n (H j) (eta j) T
      (k ≫ relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
        (H i) (H j) (eta i) (eta j))
    have h12 : P1 = P2 := actualChartUniversalWholeFamily_allTest_overlap_point_eq001
      F (U i) (U j) n (H i) (H j) (eta i) (eta j) T k
    have h23 : P2 = P3 := congrArg
      (fun q : T ⟶ H i => (relativeFiniteFlatHilbertFunctor197 F n).map q.op
        (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i))) hKi
    have h34 : P3 = P4 :=
      (relativeOpenChartClassifiedAmbientPoint_eq_pullback001 F (U i) n (H i) (eta i) T g).symm
    have h45 : P4 = P5 := hFamily
    exact h01.trans (h12.trans (h23.trans (h34.trans h45)))

  have hPair := (relativeOpenChartParameterGlued_pairSliceCartesian001 F U n H eta i j).w
  apply Over.OverMorphism.ext
  calc
    g.left ≫ (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).left =
        (k.left ≫ (relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n
          (H i) (eta i)).left) ≫
            (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).left :=
      congrArg (fun f => f ≫ (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).left)
        (congrArg (fun f => f.left) hKi).symm
    _ = k.left ≫ ((relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n
          (H i) (eta i)).left ≫
            (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).left) :=
      Category.assoc _ _ _
    _ = k.left ≫ ((relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
          (H i) (H j) (eta i) (eta j)).left ≫
            (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j).left) :=
      congrArg (k.left ≫ ·) hPair
    _ = (k.left ≫ (relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
          (H i) (H j) (eta i) (eta j)).left) ≫
            (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j).left :=
      (Category.assoc _ _ _).symm
    _ = h.left ≫ (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j).left :=
      congrArg (fun f => f ≫ (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j).left)
        (congrArg (fun f => f.left) hKt)

end PfaffianDescent
end
