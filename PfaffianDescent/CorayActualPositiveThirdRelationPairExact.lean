import PfaffianDescent.CorayActualThirdSyzygyNormalizedUnitExact
import PfaffianDescent.CorayActualPositiveNativeWholeRelationMatrix
import PfaffianDescent.CorayActualPositiveNativeChartZeroDetection
import PfaffianDescent.OpenPullbackMono

/-! The literal new S→R positive relation pair is globally exact.
SOURCE ONLY UNVERIFIED. No supplied native square/global exactness.
The two generic reflection proofs below repeat the existing four-open
mechanism for this new three-free-term complex; original maps retained. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem thirdSchemeModule_exact_of_isoPullback
    {X Y : Scheme.{u}} (e : X ≅ Y) (S : ShortComplex X.Modules)
    (h : (S.map (Scheme.Modules.pullback e.inv)).Exact) : S.Exact := by
  let P := Scheme.Modules.pullback e.inv
  let Q := Scheme.Modules.pullback e.hom
  letI : Q.PreservesHomology := Q.preservesHomology_of_preservesMonos_and_cokernels
  have hback : (S.map (P ⋙ Q)).Exact := h.map Q
  let E : P ⋙ Q ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  exact ShortComplex.exact_of_iso (S.mapNatIso E) hback

private theorem thirdSchemeModule_exact_of_openFamily_restrict_exact
    {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (S : ShortComplex X.Modules)
    (hl : ∀ i, (S.map (Scheme.Modules.restrictFunctor (U i).ι)).Exact) : S.Exact := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  let pzeroT : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  let ST := @ShortComplex.map _ _ _ _ _ _ S T pzeroT
  change ST.Exact
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact ST).mpr
  intro x
  obtain ⟨i, hi⟩ := hcover x
  let y : (U i : Scheme) := ⟨x, hi⟩
  let G := schemeModuleStalkFunctor (U i : Scheme) y
  letI : G.PreservesHomology := G.preservesHomology_of_preservesMonos_and_cokernels
  have hlocal : (S.map (Scheme.Modules.restrictFunctor (U i).ι ⋙ G)).Exact := (hl i).map G
  change (S.map (schemeModuleStalkFunctor X x)).Exact
  exact ShortComplex.exact_of_iso
    (S.mapNatIso (Scheme.Modules.restrictStalkNatIso (U i).ι y)) hlocal

private theorem thirdSchemeModule_exact_of_fourAway
    (S : ShortComplex (Proj PS).Modules)
    (h : ∀ j : Fin 4, (S.map (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)))).Exact) :
    S.Exact := by
  refine thirdSchemeModule_exact_of_openFamily_restrict_exact
    (p3StandardOpen (K := K)) ?_ S ?_
  · intro x
    have hx : x ∈ (⨆ j : Fin 4, p3StandardOpen (K := K) j) := by
      rw [p3StandardOpen_iSup K]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  · intro j
    let U := Proj.basicOpen PS (X j)
    let E := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
    let R := Scheme.Modules.restrictFunctor U.ι
    let P := Scheme.Modules.pullback E.inv
    have hp : (S.map (R ⋙ P)).Exact := ShortComplex.exact_of_iso
      (S.mapNatIso (actualPositiveNativeChartRestrictionIso (K := K) j)) (h j)
    exact thirdSchemeModule_exact_of_isoPullback E (S.map R) hp

theorem actualPositiveFiniteRelationPair_comp_eq_zero
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (s : ι₂ → κ → A) (f : ι₂ → ℕ)
    (hs : ∀ l, ActualWeightedPolynomialHomogeneous e (f l) (s l))
    (hspanR : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hspanS : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker)
    (m : ℕ) (he : ∀ a, e a ≤ m) (hf : ∀ l, f l ≤ m) :
    actualPositiveFiniteRelationMap e s f hs m hf ≫
      actualPositiveFiniteRelationMap d r e hr m he = 0 := by
  apply actualPositiveNativeCharts_jointlyDetectZero
  intro j
  let Q := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let E₁ := actualPositiveNativeWholeGeneratorFrame (K := K) j f m
  let E₂ := actualPositiveNativeWholeGeneratorFrame (K := K) j e m
  let E₃ := actualPositiveNativeWholeGeneratorFrame (K := K) j d m
  let R := actualPositiveFiniteRelationMap d r e hr m he
  let S := actualPositiveFiniteRelationMap e s f hs m hf
  let T := actualNormalizedSpecUnitRelationPairComplex g r s hspanR hspanS j
  have hframed : E₁.inv ≫ Q.map (S ≫ R) ≫ E₃.hom = 0 := by
    calc
      _ = (E₁.inv ≫ Q.map S ≫ E₂.hom) ≫ (E₂.inv ≫ Q.map R ≫ E₃.hom) := by
        simp only [Functor.map_comp, Category.assoc, E₂.hom_inv_id_assoc]
      _ = 0 := by
        rw [actualPositiveFiniteRelationMap_nativeWholeMatrix e s f hs m hf j,
          actualPositiveFiniteRelationMap_nativeWholeMatrix d r e hr m he j]
        exact T.zero
  apply (cancel_epi E₁.inv).mp
  apply (cancel_mono E₃.hom).mp
  simpa only [Category.assoc, comp_zero, zero_comp] using hframed

def actualPositiveFiniteRelationPairComplex
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (s : ι₂ → κ → A) (f : ι₂ → ℕ)
    (hs : ∀ l, ActualWeightedPolynomialHomogeneous e (f l) (s l))
    (hspanR : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hspanS : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker)
    (m : ℕ) (he : ∀ a, e a ≤ m) (hf : ∀ l, f l ≤ m) :
    ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (actualPositiveFiniteRelationMap e s f hs m hf)
    (actualPositiveFiniteRelationMap d r e hr m he)
    (actualPositiveFiniteRelationPair_comp_eq_zero g d r e hr s f hs hspanR hspanS m he hf)

theorem actualPositiveFiniteRelationPairComplex_nativeChart_exact
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (s : ι₂ → κ → A) (f : ι₂ → ℕ)
    (hs : ∀ l, ActualWeightedPolynomialHomogeneous e (f l) (s l))
    (hspanR : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hspanS : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker)
    (m : ℕ) (he : ∀ a, e a ≤ m) (hf : ∀ l, f l ≤ m) (j : Fin 4) :
    ((actualPositiveFiniteRelationPairComplex g d r e hr s f hs hspanR hspanS m he hf).map
      (Scheme.Modules.pullback
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)))).Exact := by
  let Q := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let S := actualPositiveFiniteRelationPairComplex g d r e hr s f hs hspanR hspanS m he hf
  let T := actualNormalizedSpecUnitRelationPairComplex g r s hspanR hspanS j
  let E₁ := actualPositiveNativeWholeGeneratorFrame (K := K) j f m
  let E₂ := actualPositiveNativeWholeGeneratorFrame (K := K) j e m
  let E₃ := actualPositiveNativeWholeGeneratorFrame (K := K) j d m
  have hS : E₁.inv ≫ (S.map Q).f ≫ E₂.hom = T.f :=
    actualPositiveFiniteRelationMap_nativeWholeMatrix e s f hs m hf j
  have hR : E₂.inv ≫ (S.map Q).g ≫ E₃.hom = T.g :=
    actualPositiveFiniteRelationMap_nativeWholeMatrix d r e hr m he j
  let E : S.map Q ≅ T := ShortComplex.isoMk E₁ E₂ E₃
    (((E₁.inv_comp_eq).mp hS).symm) (((E₂.inv_comp_eq).mp hR).symm)
  exact ShortComplex.exact_of_iso E.symm
    (actualNormalizedSpecUnitRelationPairComplex_exact g r s hspanR hspanS j)

theorem actualPositiveFiniteRelationPairComplex_exact
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (s : ι₂ → κ → A) (f : ι₂ → ℕ)
    (hs : ∀ l, ActualWeightedPolynomialHomogeneous e (f l) (s l))
    (hspanR : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hspanS : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker)
    (m : ℕ) (he : ∀ a, e a ≤ m) (hf : ∀ l, f l ≤ m) :
    (actualPositiveFiniteRelationPairComplex g d r e hr s f hs hspanR hspanS m he hf).Exact :=
  thirdSchemeModule_exact_of_fourAway _
    (fun j => actualPositiveFiniteRelationPairComplex_nativeChart_exact
      g d r e hr s f hs hspanR hspanS m he hf j)

end PfaffianDescent.Coray
