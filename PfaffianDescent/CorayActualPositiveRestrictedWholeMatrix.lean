import PfaffianDescent.CorayActualPositiveRestrictedUnitCoefficient
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Whole actual finite-coproduct matrix conjugation on each original open
chart. Every frame/coefficient is constructed; no matrix-comparison premise.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist BundleSectionZeroLocus
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private lemma coproductFrame_inv_component
    {C D : Type*} [Category C] [Category D] {ι : Type u}
    (F : C ⥤ D) (f : ι → C) (g : ι → D)
    [HasCoproduct f] [HasCoproductsOfShape ι D]
    [PreservesColimit (Discrete.functor f) F]
    (e : ∀ i, F.obj (f i) ≅ g i) (i : ι) :
    Sigma.ι g i ≫ (PreservesCoproduct.iso F f ≪≫ Sigma.mapIso e).inv =
      (e i).inv ≫ F.map (Sigma.ι f i) := by
  change Sigma.ι g i ≫ (Sigma.mapIso e).inv ≫ (PreservesCoproduct.iso F f).inv = _
  rw [PreservesCoproduct.inv_hom]
  calc
    _ = (Sigma.ι g i ≫ (Sigma.mapIso e).inv) ≫ sigmaComparison F f :=
      (Category.assoc _ _ _).symm
    _ = ((e i).inv ≫ Sigma.ι (fun i => F.obj (f i)) i) ≫ sigmaComparison F f :=
      congrArg (fun k => k ≫ sigmaComparison F f) (Sigma.ι_mapIso_inv e i)
    _ = (e i).inv ≫ (Sigma.ι (fun i => F.obj (f i)) i ≫ sigmaComparison F f) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun k => (e i).inv ≫ k) (ι_comp_sigmaComparison F f i)

private lemma coproductFrame_hom_component
    {C D : Type*} [Category C] [Category D] {ι : Type u}
    (F : C ⥤ D) (f : ι → C) (g : ι → D)
    [HasCoproduct f] [HasCoproductsOfShape ι D]
    [PreservesColimit (Discrete.functor f) F]
    (e : ∀ i, F.obj (f i) ≅ g i) (i : ι) :
    F.map (Sigma.ι f i) ≫ (PreservesCoproduct.iso F f ≪≫ Sigma.mapIso e).hom =
      (e i).hom ≫ Sigma.ι g i := by
  let E := PreservesCoproduct.iso F f ≪≫ Sigma.mapIso e
  have h := coproductFrame_inv_component F f g e i
  have hi : ((e i).hom ≫ Sigma.ι g i) ≫ E.inv = F.map (Sigma.ι f i) := by
    calc
      _ = (e i).hom ≫ (Sigma.ι g i ≫ E.inv) := Category.assoc _ _ _
      _ = (e i).hom ≫ (e i).inv ≫ F.map (Sigma.ι f i) :=
        congrArg (fun k => (e i).hom ≫ k) h
      _ = _ := (e i).hom_inv_id_assoc _
  exact ((Iso.comp_inv_eq E).mp hi).symm

private lemma coproductFrame_column
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {ι : Type u} [Fintype ι]
    (F : C ⥤ D) [F.Additive] (f : ι → C) (g : ι → D)
    [HasCoproduct f] [HasCoproductsOfShape ι D]
    [PreservesColimit (Discrete.functor f) F]
    (e : ∀ i, F.obj (f i) ≅ g i) {M : C} {N : D}
    (ea : F.obj M ≅ N) (r : ∀ i, M ⟶ f i) :
    ea.inv ≫ F.map (∑ i, r i ≫ Sigma.ι f i) ≫
        (PreservesCoproduct.iso F f ≪≫ Sigma.mapIso e).hom =
      ∑ i, (ea.inv ≫ F.map (r i) ≫ (e i).hom) ≫ Sigma.ι g i := by
  simp only [Functor.map_sum, Functor.map_comp, Preadditive.sum_comp,
    Preadditive.comp_sum, Category.assoc]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coproductFrame_hom_component F f g e i]

/-- Actual restricted finite-coproduct chart frame, with the original
coordinate positive unit frame on each complementary-degree summand. -/
def actualRestrictedPositiveFiniteCoproductUnitIso
    {ι : Type u} [Fintype ι] (j : Fin 4) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) (d : ι → ℕ) (m : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (∐ fun i => positiveSheafOfModules PS (m - d i)) ≅
      (∐ fun _ : ι => SheafOfModules.unit (U : Scheme).ringCatSheaf) :=
  PreservesCoproduct.iso (Scheme.Modules.restrictFunctor U.ι)
    (fun i => positiveSheafOfModules PS (m - d i)) ≪≫
      Sigma.mapIso (fun i => p3PositiveTwistOpenIsoUnit K U j hU (m - d i))

/-- Whole native normalized generator matrix on the restricted chart. -/
def actualRestrictedPositiveUnitGeneratorMatrix
    {ι : Type u} [Fintype ι] (j : Fin 4) (U : (Proj PS).Opens)
    (hU : U ≤ p3StandardOpen (K := K) j) (g : ι → A) :
    (∐ fun _ : ι => SheafOfModules.unit (U : Scheme).ringCatSheaf) ⟶
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
  Sigma.desc (fun i => unitEndomorphismOfRegularFunction
    (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (g i))))

/-- Whole native normalized relation matrix on the restricted chart. -/
def actualRestrictedPositiveUnitRelationMatrix
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (j : Fin 4) (U : (Proj PS).Opens) (hU : U ≤ p3StandardOpen (K := K) j)
    (r : κ → ι → A) :
    (∐ fun _ : κ => SheafOfModules.unit (U : Scheme).ringCatSheaf) ⟶
      (∐ fun _ : ι => SheafOfModules.unit (U : Scheme).ringCatSheaf) :=
  Sigma.desc (fun a => ∑ i,
    unitEndomorphismOfRegularFunction
      (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (r a i))) ≫
        Sigma.ι (fun _ : ι => SheafOfModules.unit (U : Scheme).ringCatSheaf) i)

private lemma fourComp_congr_firstTwo
    {C : Type*} [Category C] {W X X' Y Z T : C}
    (a : W ⟶ X) (b : X ⟶ Y) (a' : W ⟶ X') (b' : X' ⟶ Y)
    (c : Y ⟶ Z) (d : Z ⟶ T) (h : a ≫ b = a' ≫ b') :
    a ≫ b ≫ c ≫ d = a' ≫ b' ≫ c ≫ d :=
  (Category.assoc a b (c ≫ d)).symm.trans
    ((congrArg (fun k => k ≫ c ≫ d) h).trans (Category.assoc a' b' (c ≫ d)))

private lemma fourComp_middle
    {C : Type*} [Category C] {W X Y Z T : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T)
    (p : X ⟶ Z) (h : b ≫ c = p) : a ≫ b ≫ c ≫ d = a ≫ p ≫ d :=
  (congrArg (fun k => a ≫ k) (Category.assoc b c d).symm).trans
    (congrArg (fun k => a ≫ k ≫ d) h)

/-- Genuine WHOLE generator-matrix conjugation, derived from actual unit
coefficients and actual coproduct inclusions. -/
theorem actualPositiveFiniteGeneratorMap_restrictedWholeMatrix
    {ι : Type u} [Fintype ι] (g : ι → A) (d : ι → ℕ)
    (hg : ∀ i, (g i).IsHomogeneous (d i)) (m : ℕ) (hm : ∀ i, d i ≤ m)
    (j : Fin 4) (U : (Proj PS).Opens) (hU : U ≤ p3StandardOpen (K := K) j) :
    (actualRestrictedPositiveFiniteCoproductUnitIso j U hU d m).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (actualPositiveFiniteGeneratorMap g d hg m hm) ≫
      (p3PositiveTwistOpenIsoUnit K U j hU m).hom =
    actualRestrictedPositiveUnitGeneratorMatrix j U hU g := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let f : ι → (Proj PS).Modules := fun i => positiveSheafOfModules PS (m - d i)
  let O : (U : Scheme).Modules := SheafOfModules.unit (U : Scheme).ringCatSheaf
  let units : ι → (U : Scheme).Modules := fun _ => O
  let e : ∀ i, F.obj (f i) ≅ units i :=
    fun i => p3PositiveTwistOpenIsoUnit K U j hU (m - d i)
  let E : F.obj (∐ f) ≅ ∐ units := actualRestrictedPositiveFiniteCoproductUnitIso j U hU d m
  let em : F.obj (positiveSheafOfModules PS m) ≅ O :=
    p3PositiveTwistOpenIsoUnit K U j hU m
  let G := actualPositiveFiniteGeneratorMap g d hg m hm
  apply Sigma.hom_ext
  intro i
  let w := actualPositiveWeightedMultiplication (g i) (hg i)
    (m - d i) m (by have := hm i; omega)
  have hc : Sigma.ι units i ≫ E.inv = (e i).inv ≫ F.map (Sigma.ι f i) :=
    coproductFrame_inv_component F f units e i
  have hgcomp : F.map (Sigma.ι f i) ≫ F.map G = F.map w :=
    (F.map_comp _ _).symm.trans
      (congrArg F.map (actualPositiveFiniteGeneratorMap_component g d hg m hm i))
  have h₁ : Sigma.ι units i ≫ E.inv ≫ F.map G ≫ em.hom =
      (e i).inv ≫ F.map (Sigma.ι f i) ≫ F.map G ≫ em.hom := by
    exact fourComp_congr_firstTwo (C := (U : Scheme).Modules)
      (Sigma.ι units i) E.inv (e i).inv (F.map (Sigma.ι f i)) (F.map G) em.hom hc
  have h₂ : (e i).inv ≫ F.map (Sigma.ι f i) ≫ F.map G ≫ em.hom =
      (e i).inv ≫ F.map w ≫ em.hom := by
    exact fourComp_middle (C := (U : Scheme).Modules)
      (e i).inv (F.map (Sigma.ι f i)) (F.map G) em.hom (F.map w) hgcomp
  have h₃ : (e i).inv ≫ F.map w ≫ em.hom =
      unitEndomorphismOfRegularFunction
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (g i))) :=
    actualPositiveWeightedMultiplication_restrictedUnitCoefficient
      j (g i) (hg i) (m - d i) m _ U hU
  have h₄ : unitEndomorphismOfRegularFunction
      (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (g i))) =
      Sigma.ι units i ≫ actualRestrictedPositiveUnitGeneratorMatrix j U hU g :=
    (Sigma.ι_desc (C := (U : Scheme).Modules) (f := units)
      (fun k : ι => unitEndomorphismOfRegularFunction
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (g k)))) i).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

private lemma framedZero
    {C : Type*} [Category C] [HasZeroMorphisms C] {M N O : C}
    (a : O ⟶ M) (b : N ⟶ O) : a ≫ (0 : M ⟶ N) ≫ b = (0 : O ⟶ O) := by
  simp only [zero_comp, comp_zero]

private lemma actualPositiveFiniteRelationEntry_restrictedUnitCoefficient
    {ι : Type u} (d : ι → ℕ) (r : ι → A) (e : ℕ)
    (hr : ActualWeightedPolynomialHomogeneous d e r)
    (m : ℕ) (hm : e ≤ m) (i : ι)
    (j : Fin 4) (U : (Proj PS).Opens) (hU : U ≤ p3StandardOpen (K := K) j) :
    (p3PositiveTwistOpenIsoUnit K U j hU (m - e)).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (actualPositiveFiniteRelationEntry d r e hr m hm i) ≫
      (p3PositiveTwistOpenIsoUnit K U j hU (m - d i)).hom =
      unitEndomorphismOfRegularFunction
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (r i))) := by
  classical
  by_cases hi : d i ≤ e
  · rw [actualPositiveFiniteRelationEntry_of_weight_le d r e hr m hm i hi]
    exact actualPositiveWeightedMultiplication_restrictedUnitCoefficient
      j (r i) (hr i).1 (m - e) (m - d i) _ U hU
  · have hz : r i = 0 := (hr i).2 (Nat.lt_of_not_ge hi)
    have hentry := (actualPositiveFiniteRelationEntry_of_weight_lt
      d r e hr m hm i (Nat.lt_of_not_ge hi) j).1
    let F := Scheme.Modules.restrictFunctor U.ι
    let O : (U : Scheme).Modules := SheafOfModules.unit (U : Scheme).ringCatSheaf
    let a := p3PositiveTwistOpenIsoUnit K U j hU (m - e)
    let b := p3PositiveTwistOpenIsoUnit K U j hU (m - d i)
    have hmap : F.map (actualPositiveFiniteRelationEntry d r e hr m hm i) =
        (0 : F.obj (positiveSheafOfModules PS (m - e)) ⟶
          F.obj (positiveSheafOfModules PS (m - d i))) :=
      (congrArg F.map hentry).trans
        (F.map_zero (positiveSheafOfModules PS (m - e)) (positiveSheafOfModules PS (m - d i)))
    have hleft : a.inv ≫ F.map (actualPositiveFiniteRelationEntry d r e hr m hm i) ≫
        b.hom = (0 : O ⟶ O) :=
      (congrArg (fun k => a.inv ≫ k ≫ b.hom) hmap).trans
        (framedZero (C := (U : Scheme).Modules) a.inv b.hom)
    have hcoeff : U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (r i)) =
        (0 : Γ((U : Scheme), ⊤)) := by
      rw [hz]
      simp only [actualAmbientChartCoefficientSection, map_zero]
      change U.topIso.inv.hom
        (((Proj PS).presheaf.map (homOfLE hU).op).hom
          (0 : Γ(Proj PS, p3StandardOpen (K := K) j))) = 0
      exact (congrArg U.topIso.inv.hom
        ((Proj PS).presheaf.map (homOfLE hU).op).hom.map_zero).trans
          U.topIso.inv.hom.map_zero
    have hright : unitEndomorphismOfRegularFunction
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (r i))) =
        (0 : O ⟶ O) :=
      (congrArg (unitEndomorphismOfRegularFunction (X := (U : Scheme))) hcoeff).trans
        (unitEndomorphismOfRegularFunction_zero (X := (U : Scheme)))
    exact hleft.trans hright.symm

/-- Genuine WHOLE relation-matrix conjugation, including all forced-zero
entries. The literal relation matrix is kept, not replaced by an arbitrary
kernel map chosen after passing to sheaves. -/
theorem actualPositiveFiniteRelationMap_restrictedWholeMatrix
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (m : ℕ) (hm : ∀ a, e a ≤ m)
    (j : Fin 4) (U : (Proj PS).Opens) (hU : U ≤ p3StandardOpen (K := K) j) :
    (actualRestrictedPositiveFiniteCoproductUnitIso j U hU e m).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (actualPositiveFiniteRelationMap d r e hr m hm) ≫
      (actualRestrictedPositiveFiniteCoproductUnitIso j U hU d m).hom =
    actualRestrictedPositiveUnitRelationMatrix j U hU r := by
  classical
  let F := Scheme.Modules.restrictFunctor U.ι
  letI : F.Additive :=
    Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  let fd : ι → (Proj PS).Modules := fun i => positiveSheafOfModules PS (m - d i)
  let fe : κ → (Proj PS).Modules := fun a => positiveSheafOfModules PS (m - e a)
  let O : (U : Scheme).Modules := SheafOfModules.unit (U : Scheme).ringCatSheaf
  let ud : ι → (U : Scheme).Modules := fun _ => O
  let ue : κ → (U : Scheme).Modules := fun _ => O
  let ed : ∀ i, F.obj (fd i) ≅ O :=
    fun i => p3PositiveTwistOpenIsoUnit K U j hU (m - d i)
  let ee : ∀ a, F.obj (fe a) ≅ O :=
    fun a => p3PositiveTwistOpenIsoUnit K U j hU (m - e a)
  let Ed : F.obj (∐ fd) ≅ ∐ ud := actualRestrictedPositiveFiniteCoproductUnitIso j U hU d m
  let Ee : F.obj (∐ fe) ≅ ∐ ue := actualRestrictedPositiveFiniteCoproductUnitIso j U hU e m
  let R : (∐ fe) ⟶ (∐ fd) := actualPositiveFiniteRelationMap d r e hr m hm
  apply Sigma.hom_ext
  intro a
  let col : fe a ⟶ ∐ fd :=
    actualPositiveFiniteRelationColumn d (r a) (e a) (hr a) m (hm a)
  have hc : Sigma.ι ue a ≫ Ee.inv = (ee a).inv ≫ F.map (Sigma.ι fe a) :=
    coproductFrame_inv_component F fe ue ee a
  have hcol : F.map (Sigma.ι fe a) ≫ F.map R = F.map col :=
    (F.map_comp _ _).symm.trans (congrArg F.map
      (Sigma.ι_desc (C := (Proj PS).Modules) (f := fe)
        (fun b : κ => actualPositiveFiniteRelationColumn d (r b) (e b) (hr b) m (hm b)) a))
  have hcolumn := coproductFrame_column
    (C := (Proj PS).Modules) (D := (U : Scheme).Modules) F fd ud ed (ee a)
    (fun i => actualPositiveFiniteRelationEntry d (r a) (e a) (hr a) m (hm a) i)
  have h₁ : Sigma.ι ue a ≫ Ee.inv ≫ F.map R ≫ Ed.hom =
      (ee a).inv ≫ F.map (Sigma.ι fe a) ≫ F.map R ≫ Ed.hom := by
    exact fourComp_congr_firstTwo (C := (U : Scheme).Modules)
      (Sigma.ι ue a) Ee.inv (ee a).inv (F.map (Sigma.ι fe a)) (F.map R) Ed.hom hc
  have h₂ : (ee a).inv ≫ F.map (Sigma.ι fe a) ≫ F.map R ≫ Ed.hom =
      (ee a).inv ≫ F.map col ≫ Ed.hom := by
    exact fourComp_middle (C := (U : Scheme).Modules)
      (ee a).inv (F.map (Sigma.ι fe a)) (F.map R) Ed.hom (F.map col) hcol
  have h₃ : (ee a).inv ≫ F.map col ≫ Ed.hom =
      (∑ i : ι, ((ee a).inv ≫
        F.map (actualPositiveFiniteRelationEntry d (r a) (e a) (hr a) m (hm a) i) ≫
        (ed i).hom) ≫ Sigma.ι ud i : O ⟶ ∐ ud) := hcolumn
  have h₄ : (∑ i : ι, ((ee a).inv ≫
      F.map (actualPositiveFiniteRelationEntry d (r a) (e a) (hr a) m (hm a) i) ≫
      (ed i).hom) ≫ Sigma.ι ud i : O ⟶ ∐ ud) =
      (∑ i : ι, unitEndomorphismOfRegularFunction
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (r a i))) ≫
        Sigma.ι ud i : O ⟶ ∐ ud) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun k => k ≫ Sigma.ι ud i)
      (actualPositiveFiniteRelationEntry_restrictedUnitCoefficient
        d (r a) (e a) (hr a) m (hm a) i j U hU)
  have h₅ : (∑ i : ι, unitEndomorphismOfRegularFunction
      (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (r a i))) ≫
      Sigma.ι ud i : O ⟶ ∐ ud) =
      Sigma.ι ue a ≫ actualRestrictedPositiveUnitRelationMatrix j U hU r :=
    (Sigma.ι_desc (C := (U : Scheme).Modules) (f := ue)
      (fun b : κ => (∑ i : ι, unitEndomorphismOfRegularFunction
        (U.topIso.inv.hom (actualAmbientChartCoefficientSection j U hU (r b i))) ≫
          Sigma.ι ud i : O ⟶ ∐ ud)) a).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end PfaffianDescent.Coray
