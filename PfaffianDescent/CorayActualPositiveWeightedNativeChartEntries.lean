import PfaffianDescent.CorayActualPositiveFiniteCoproductPresentation
import PfaffianDescent.CorayActualPositiveChartPresentationEntries
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! The complementary-degree casts in the ACTUAL finite positive sheaf
presentation do not alter its normalized chart entries. No frame equality
is supplied by the caller. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The ACTUAL ambient native-chart positive frame. This is constructed from
restriction to the same basic open, its actual Spec isomorphism, and the
canonical pullback comparison of units. No chart frame is supplied. -/
def actualAmbientPositiveNativeChartUnitIso (j : Fin 4) (m : ℕ) :
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).obj
        (positiveSheafOfModules PS m) ≅
      SheafOfModules.unit
        (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf := by
  let U := Proj.basicOpen PS (X j)
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let M := positiveSheafOfModules PS m
  let eU : (Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫
      PfaffianDescent.ProjectiveNegativeTwist.p3PositiveTwistOpenIsoUnit K U j le_rfl m
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison e.inv) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison e.inv
  change (Scheme.Modules.pullback (e.inv ≫ U.ι)).obj M ≅ _
  exact (Scheme.Modules.pullbackComp e.inv U.ι).symm.app M ≪≫
    (Scheme.Modules.pullback e.inv).mapIso eU ≪≫
      asIso (BundleSectionZeroLocus.pullbackUnitComparison e.inv)

/-- Actual pullback preserves this finite coproduct and each positive
summand is framed by its OWN coordinate-chart unit isomorphism. -/
def actualAmbientPositiveFiniteCoproductChartUnitIso
    {ι : Type u} [Fintype ι] (j : Fin 4) (d : ι → ℕ) (m : ℕ) :
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).obj
        (∐ fun i => positiveSheafOfModules PS (m - d i)) ≅
      (∐ fun _ : ι => SheafOfModules.unit
        (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) :=
  PreservesCoproduct.iso
    (Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)))
    (fun i => positiveSheafOfModules PS (m - d i)) ≪≫
      Sigma.mapIso (fun i => actualAmbientPositiveNativeChartUnitIso j (m - d i))

private lemma finiteCoproductFrame_inv_component
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
      congrArg (fun a => a ≫ sigmaComparison F f) (Sigma.ι_mapIso_inv e i)
    _ = (e i).inv ≫ (Sigma.ι (fun i => F.obj (f i)) i ≫ sigmaComparison F f) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun a => (e i).inv ≫ a) (ι_comp_sigmaComparison F f i)

/-- The actual framed finite-coproduct inverse has its original native
pullback inclusions as components. No coproduct or action is transported. -/
theorem actualAmbientPositiveFiniteCoproductChartUnitIso_inv_component
    {ι : Type u} [Fintype ι] (j : Fin 4) (d : ι → ℕ) (m : ℕ) (i : ι) :
    Sigma.ι (fun _ : ι => SheafOfModules.unit
        (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) i ≫
      (actualAmbientPositiveFiniteCoproductChartUnitIso j d m).inv =
      (actualAmbientPositiveNativeChartUnitIso j (m - d i)).inv ≫
        (Scheme.Modules.pullback
          (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
            (Sigma.ι (fun i => positiveSheafOfModules PS (m - d i)) i) := by
  exact finiteCoproductFrame_inv_component _ _ _
    (fun i => actualAmbientPositiveNativeChartUnitIso j (m - d i)) i

/-- The actual map between complementary positive twists has the literal
normalized coefficient in its OWN positive stalk frames. The target cast
is eliminated by its defining equality, before the native producer is used. -/
theorem actualPositiveWeightedMultiplication_normalizedStalkEntry
    (j : Fin 4) {d : ℕ} (p : A) (hp : p.IsHomogeneous d)
    (a b : ℕ) (h : a + d = b)
    (x : ProjectiveSpectrum.top PS)
    (hj : X j ∈ (positivePointIdeal PS x).primeCompl)
    (z : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (positiveModulePresheaf PS a).presheaf x)) :
    positiveStalkToFractionModule PS b x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((Scheme.Modules.toPresheaf (Proj PS)).map
            (actualPositiveWeightedMultiplication p hp a b h)) z) =
      positiveLocalTrivialization PS (positivePointIdeal PS x)
        ⟨X j, isHomogeneous_X K j⟩ hj b
        (HomogeneousLocalization.mapId PS (Submonoid.powers_le.mpr hj)
            (ambientChartEvaluation j p) *
          (positiveLocalTrivialization PS (positivePointIdeal PS x)
            ⟨X j, isHomogeneous_X K j⟩ hj a).symm
              (positiveStalkToFractionModule PS a x z)) := by
  cases h
  simp only [actualPositiveWeightedMultiplication, eqToHom_refl, Category.comp_id]
  exact actualPositiveHomogeneousStalkMap_normalizedChartEntry j p hp a x hj z

/-- A generator inclusion followed by the actual finite coproduct generator
map has the original homogeneous multiplication map as its component. -/
theorem actualPositiveFiniteGeneratorMap_component
    {ι : Type u} [Fintype ι] (g : ι → A) (d : ι → ℕ)
    (hg : ∀ i, (g i).IsHomogeneous (d i))
    (m : ℕ) (hm : ∀ i, d i ≤ m) (i : ι) :
    CategoryTheory.Limits.Sigma.ι (fun i => positiveSheafOfModules PS (m - d i)) i ≫
        actualPositiveFiniteGeneratorMap g d hg m hm =
      actualPositiveWeightedMultiplication (g i) (hg i)
        (m - d i) m (by have := hm i; omega) := by
  exact CategoryTheory.Limits.Sigma.ι_desc _ _

/-- The framed pullback generator component is the SAME constructed
homogeneous multiplication conjugated by the actual coordinate frames.
This equality is proved with actual coproduct inclusions and functor maps. -/
theorem actualPositiveFiniteGeneratorMap_nativeChart_component
    {ι : Type u} [Fintype ι] (g : ι → A) (d : ι → ℕ)
    (hg : ∀ i, (g i).IsHomogeneous (d i))
    (m : ℕ) (hm : ∀ i, d i ≤ m) (j : Fin 4) (i : ι) :
    Sigma.ι (fun _ : ι => SheafOfModules.unit
        (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) i ≫
      (actualAmbientPositiveFiniteCoproductChartUnitIso j d m).inv ≫
      (Scheme.Modules.pullback
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
          (actualPositiveFiniteGeneratorMap g d hg m hm) ≫
      (actualAmbientPositiveNativeChartUnitIso j m).hom =
    (actualAmbientPositiveNativeChartUnitIso j (m - d i)).inv ≫
      (Scheme.Modules.pullback
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
          (actualPositiveWeightedMultiplication (g i) (hg i)
            (m - d i) m (by have := hm i; omega)) ≫
      (actualAmbientPositiveNativeChartUnitIso j m).hom := by
  let F := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let E := actualAmbientPositiveFiniteCoproductChartUnitIso (K := K) j d m
  let em := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  let ei := actualAmbientPositiveNativeChartUnitIso (K := K) j (m - d i)
  let s := Sigma.ι (fun _ : ι => SheafOfModules.unit
    (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) i
  let G := actualPositiveFiniteGeneratorMap g d hg m hm
  let w := actualPositiveWeightedMultiplication (g i) (hg i)
    (m - d i) m (by have := hm i; omega)
  have hc := actualAmbientPositiveFiniteCoproductChartUnitIso_inv_component (K := K) j d m i
  have hgcomp : Sigma.ι (fun i => positiveSheafOfModules PS (m - d i)) i ≫ G = w :=
    actualPositiveFiniteGeneratorMap_component g d hg m hm i
  change s ≫ E.inv ≫ F.map G ≫ em.hom = ei.inv ≫ F.map w ≫ em.hom
  let ii := Sigma.ι (fun i => positiveSheafOfModules PS (m - d i)) i
  have h₁ : s ≫ E.inv ≫ F.map G ≫ em.hom =
      (s ≫ E.inv) ≫ F.map G ≫ em.hom :=
    (Category.assoc s E.inv (F.map G ≫ em.hom)).symm
  have h₂ : (s ≫ E.inv) ≫ F.map G ≫ em.hom =
      (ei.inv ≫ F.map ii) ≫ F.map G ≫ em.hom :=
    congrArg (fun a => a ≫ F.map G ≫ em.hom) hc
  have h₃ : (ei.inv ≫ F.map ii) ≫ F.map G ≫ em.hom =
      ei.inv ≫ F.map (ii ≫ G) ≫ em.hom :=
    (Category.assoc ei.inv (F.map ii) (F.map G ≫ em.hom)).trans
      (congrArg (fun a => ei.inv ≫ a) (F.map_comp_assoc ii G em.hom).symm)
  have h₄ : ei.inv ≫ F.map (ii ≫ G) ≫ em.hom =
      ei.inv ≫ F.map w ≫ em.hom :=
    congrArg (fun a => ei.inv ≫ F.map a ≫ em.hom) hgcomp
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- Every nonzero-weight relation entry has exactly its literal normalized
polynomial coefficient. The native map is the constructed sheaf entry. -/
theorem actualPositiveFiniteRelationEntry_of_weight_le
    {ι : Type u} (d : ι → ℕ) (r : ι → A) (e : ℕ)
    (hr : ActualWeightedPolynomialHomogeneous d e r)
    (m : ℕ) (hm : e ≤ m) (i : ι) (hi : d i ≤ e) :
    actualPositiveFiniteRelationEntry d r e hr m hm i =
      actualPositiveWeightedMultiplication (r i) (hr i).1
        (m - e) (m - d i) (by omega) := by
  classical
  simp only [actualPositiveFiniteRelationEntry, dif_pos hi]

/-- A relation entry below a generator weight is zero both as a sheaf map
and as the literal normalized chart coefficient. -/
theorem actualPositiveFiniteRelationEntry_of_weight_lt
    {ι : Type u} (d : ι → ℕ) (r : ι → A) (e : ℕ)
    (hr : ActualWeightedPolynomialHomogeneous d e r)
    (m : ℕ) (hm : e ≤ m) (i : ι) (hi : e < d i) (j : Fin 4) :
    actualPositiveFiniteRelationEntry d r e hr m hm i = 0 ∧
      ambientChartEvaluation j (r i) = 0 := by
  classical
  refine ⟨?_, ?_⟩
  · simp only [actualPositiveFiniteRelationEntry, dif_neg (Nat.not_le.mpr hi)]
  · rw [(hr i).2 hi, map_zero]

end PfaffianDescent.Coray
