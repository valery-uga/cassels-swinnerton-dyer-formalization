import PfaffianDescent.CorayActualBasicOpenSpecUnitMatrix
import PfaffianDescent.OpenPullbackMono

/-! Exactness of the SAME global finite positive-twist presentation, derived
on the original four coordinate opens from canonical native matrix comparison.
No global exactness or Serre conclusion is an input. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem framedMatrices_zero
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (S : ShortComplex C) {M₁ M₂ M₃ : C}
    (e₁ : M₁ ≅ S.X₁) (e₂ : M₂ ≅ S.X₂) (e₃ : S.X₃ ≅ M₃)
    (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
    (hf : e₁.hom ≫ S.f ≫ e₂.inv = f)
    (hg : e₂.hom ≫ S.g ≫ e₃.hom = g) : f ≫ g = 0 := by
  rw [← hf, ← hg]
  simp only [Category.assoc, e₂.inv_hom_id_assoc, S.zero_assoc, comp_zero, zero_comp]

private theorem schemeModule_exact_of_isoPullback
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

/-- Every literal column is in the OWN polynomial generator kernel,
internally derived from the SAME spanning-relation hypothesis. -/
theorem actualPresentationRelation_mem_kernel
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker) :
    ∀ a, actualPolynomialGeneratorMap g (r a) = 0 := by
  intro a
  apply LinearMap.mem_ker.mp
  rw [← hr]
  exact Submodule.subset_span ⟨a, rfl⟩

private def actualOriginalRestrictedUnitComplex
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (d : ι → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (hker : ∀ a, actualPolynomialGeneratorMap g (r a) = 0)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : ∀ a, e a ≤ m) (j : Fin 4) :
    ShortComplex (Proj.basicOpen PS (X j) : Scheme).Modules := by
  let U := Proj.basicOpen PS (X j)
  let R := Scheme.Modules.restrictFunctor U.ι
  let S := (actualPositiveFinitePresentationComplex g d hg r e hr hker m hd he).map R
  let E₁ := actualRestrictedPositiveFiniteCoproductUnitIso (K := K) j U le_rfl e m
  let E₂ := actualRestrictedPositiveFiniteCoproductUnitIso (K := K) j U le_rfl d m
  let E₃ := p3PositiveTwistOpenIsoUnit K U j le_rfl m
  exact ShortComplex.mk (actualRestrictedPositiveUnitRelationMatrix j U le_rfl r)
    (actualRestrictedPositiveUnitGeneratorMatrix j U le_rfl g)
    (framedMatrices_zero S E₁.symm E₂.symm E₃ _ _
      (actualPositiveFiniteRelationMap_restrictedWholeMatrix d r e hr m he j U le_rfl)
      (actualPositiveFiniteGeneratorMap_restrictedWholeMatrix g d hg m hd j U le_rfl))

/-- The ORIGINAL presentation restricts to an exact complex on every actual
standard open. Canonical Spec pullback and native matrix exactness discharge
this conclusion internally; no local sheaf certificate is supplied. -/
theorem actualPositiveFinitePresentationComplex_restrict_exact
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (d : ι → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (hspanG : Ideal.span (Set.range g) = I.toIdeal)
    (hspanR : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : ∀ a, e a ≤ m) (j : Fin 4) :
    ((actualPositiveFinitePresentationComplex g d hg r e hr
      (actualPresentationRelation_mem_kernel g r hspanR) m hd he).map
        (Scheme.Modules.restrictFunctor (Proj.basicOpen PS (X j)).ι)).Exact := by
  let hker := actualPresentationRelation_mem_kernel g r hspanR
  let U := Proj.basicOpen PS (X j)
  let E := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback E.inv
  let R := Scheme.Modules.restrictFunctor U.ι
  let S := (actualPositiveFinitePresentationComplex g d hg r e hr hker m hd he).map R
  let T := actualOriginalRestrictedUnitComplex g d hg r e hr hker m hd he j
  let N := actualNormalizedSpecUnitPresentationComplex I g r hspanG hspanR j
  let uκ := actualCanonicalPullbackUnitCoproductIso E.inv κ
  let uι := actualCanonicalPullbackUnitCoproductIso E.inv ι
  let u := actualCanonicalPullbackUnitIso E.inv
  have hRP : uκ.inv ≫ (T.map P).f ≫ uι.hom = N.f :=
    actualRestrictedPositiveUnitRelationMatrix_basicOpenPullback j r
  have hGP : uι.inv ≫ (T.map P).g ≫ u.hom = N.g :=
    actualRestrictedPositiveUnitGeneratorMatrix_basicOpenPullback j g
  let eP : T.map P ≅ N := ShortComplex.isoMk uκ uι u
    (((uκ.inv_comp_eq).mp hRP).symm)
    (((uι.inv_comp_eq).mp hGP).symm)
  have hTP : (T.map P).Exact := ShortComplex.exact_of_iso eP.symm
    (actualNormalizedSpecUnitPresentationComplex_exact I g r hspanG hspanR j)
  have hT : T.Exact := schemeModule_exact_of_isoPullback E T hTP
  let E₁ := actualRestrictedPositiveFiniteCoproductUnitIso (K := K) j U le_rfl e m
  let E₂ := actualRestrictedPositiveFiniteCoproductUnitIso (K := K) j U le_rfl d m
  let E₃ := p3PositiveTwistOpenIsoUnit K U j le_rfl m
  have hR : E₁.inv ≫ S.f ≫ E₂.hom = T.f :=
    actualPositiveFiniteRelationMap_restrictedWholeMatrix d r e hr m he j U le_rfl
  have hG : E₂.inv ≫ S.g ≫ E₃.hom = T.g :=
    actualPositiveFiniteGeneratorMap_restrictedWholeMatrix g d hg m hd j U le_rfl
  let eS : S ≅ T := ShortComplex.isoMk E₁ E₂ E₃
    (((E₁.inv_comp_eq).mp hR).symm)
    (((E₂.inv_comp_eq).mp hG).symm)
  exact ShortComplex.exact_of_iso eS.symm hT

private theorem schemeModule_exact_of_openFamily_restrict_exact
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

/-- Global native exactness of the SAME finite positive-twist presentation
of the OWN whole homogeneous ideal. Neither global exactness, canonical
section surjectivity nor a Serre conclusion is assumed. -/
theorem actualPositiveFinitePresentationComplex_exact
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (d : ι → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (hspanG : Ideal.span (Set.range g) = I.toIdeal)
    (hspanR : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : ∀ a, e a ≤ m) :
    (actualPositiveFinitePresentationComplex g d hg r e hr
      (actualPresentationRelation_mem_kernel g r hspanR) m hd he).Exact := by
  have hcover : ∀ x : Proj PS, ∃ j : Fin 4, x ∈ p3StandardOpen (K := K) j := by
    intro x
    have hx : x ∈ (⨆ j : Fin 4, p3StandardOpen (K := K) j) := by
      rw [p3StandardOpen_iSup K]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  apply schemeModule_exact_of_openFamily_restrict_exact (p3StandardOpen (K := K)) hcover
  intro j
  exact actualPositiveFinitePresentationComplex_restrict_exact
    I g d hg r e hr hspanG hspanR m hd he j

/-- Every OWN whole homogeneous ideal internally supplies a finite positive
presentation which is globally exact in every degree above its actual
weights. No supplied matrix, sheaf exactness or geometric certificate. -/
theorem homogeneousIdeal_exists_actualPositiveFinitePresentation_exact
    (I : HomogeneousIdeal PS) :
    ∃ (T : Finset A) (d : T → ℕ) (R : Finset (T → A)) (e : R → ℕ) (B : ℕ)
      (hg : ∀ i : T, (i : A).IsHomogeneous (d i))
      (hr : ∀ a : R, ActualWeightedPolynomialHomogeneous d (e a) a.val)
      (hker : ∀ a : R, actualPolynomialGeneratorMap (fun i : T => i.val) a.val = 0),
      Ideal.span (T : Set A) = I.toIdeal ∧
      Submodule.span A (R : Set (T → A)) =
        (actualPolynomialGeneratorMap (fun i : T => i.val)).ker ∧
      (∀ i : T, d i ≤ B) ∧ (∀ a : R, e a ≤ B) ∧
      ∀ (m : ℕ) (hd : ∀ i : T, d i ≤ m) (he : ∀ a : R, e a ≤ m),
        (actualPositiveFinitePresentationComplex (fun i : T => i.val) d hg
          (fun a : R => a.val) e hr hker m hd he).Exact := by
  classical
  obtain ⟨T, d, R, e, B, hT, hd, hR, he, hker, hchart⟩ :=
    homogeneousIdeal_exists_actualPositiveFiniteCoproductPresentationData I
  have hTset : Set.range (fun i : T => i.val) = (T : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩; exact i.property
    · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
  have hRset : Set.range (fun a : R => a.val) = (R : Set (T → A)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩; exact i.property
    · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
  have hspanG : Ideal.span (Set.range (fun i : T => i.val)) = I.toIdeal := by
    rw [hTset]; exact hT
  have hspanR : Submodule.span A (Set.range (fun a : R => a.val)) =
      (actualPolynomialGeneratorMap (fun i : T => i.val)).ker := by
    rw [hRset]; exact hR
  refine ⟨T, d, R, e, B, fun i => (hd i).2, fun a => (he a).2,
    hker, hT, hR, fun i => (hd i).1, fun a => (he a).1, ?_⟩
  intro m hdm hem
  exact actualPositiveFinitePresentationComplex_exact I (fun i : T => i.val) d
    (fun i => (hd i).2) (fun a : R => a.val) e (fun a => (he a).2)
    hspanG hspanR m hdm hem

end PfaffianDescent.Coray
