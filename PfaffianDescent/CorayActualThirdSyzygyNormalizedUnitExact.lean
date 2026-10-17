import PfaffianDescent.CorayActualThirdSyzygyDegreeZeroChartExact
import PfaffianDescent.CorayActualNormalizedSpecUnitMatrixExact

/-! Actual normalized tilde and unit matrices for the new relation pair.
Source only, UNVERIFIED. No native comparison/exactness premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

def actualDegreeZeroChartRelationPair_complex
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (r : κ → ι → A) (s : ι₂ → κ → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hs : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker) (j : Fin 4) :
    ShortComplex (ModuleCat.{u} (HomogeneousLocalization.Away PS (X j))) :=
  ModuleCat.shortComplexOfCompEqZero
    (actualDegreeZeroChartRelationMap j s) (actualDegreeZeroChartRelationMap j r) (by
      apply LinearMap.ext
      intro x
      exact (actualDegreeZeroChartRelationPair_exact g r s hr hs j _).mpr ⟨x, rfl⟩)

def actualDegreeZeroChartRelationPair_tildeComplex
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (r : κ → ι → A) (s : ι₂ → κ → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hs : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker) (j : Fin 4) :
    ShortComplex (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules := by
  let F := tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  exact (actualDegreeZeroChartRelationPair_complex g r s hr hs j).map F

theorem actualDegreeZeroChartRelationPair_tildeComplex_exact
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (r : κ → ι → A) (s : ι₂ → κ → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hs : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker) (j : Fin 4) :
    (actualDegreeZeroChartRelationPair_tildeComplex g r s hr hs j).Exact := by
  let F := tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  letI : F.PreservesMonomorphisms := PfaffianDescent.tilde_preservesMonomorphisms
    (R := CommRingCat.of (HomogeneousLocalization.Away PS (X j)))
  letI : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  have h : (actualDegreeZeroChartRelationPair_complex g r s hr hs j).Exact :=
    ModuleCat.shortComplex_exact _ (actualDegreeZeroChartRelationPair_exact g r s hr hs j)
  change ((actualDegreeZeroChartRelationPair_complex g r s hr hs j).map F).Exact
  exact h.map F

private theorem thirdUnitFramedMatrices_zero
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (S : ShortComplex C) {M₁ M₂ M₃ : C}
    (e₁ : M₁ ≅ S.X₁) (e₂ : M₂ ≅ S.X₂) (e₃ : S.X₃ ≅ M₃)
    (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
    (hf : e₁.hom ≫ S.f ≫ e₂.inv = f)
    (hg : e₂.hom ≫ S.g ≫ e₃.hom = g) : f ≫ g = 0 := by
  rw [← hf, ← hg]
  simp only [Category.assoc, e₂.inv_hom_id_assoc, S.zero_assoc, comp_zero, zero_comp]

def actualNormalizedSpecUnitRelationPairComplex
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (r : κ → ι → A) (s : ι₂ → κ → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hs : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker) (j : Fin 4) :
    ShortComplex (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules :=
  ShortComplex.mk (actualNormalizedSpecUnitRelationMatrix j s)
    (actualNormalizedSpecUnitRelationMatrix j r)
    (thirdUnitFramedMatrices_zero (actualDegreeZeroChartRelationPair_tildeComplex g r s hr hs j)
      (actualFinitePiTildeUnitIso _ ι₂) (actualFinitePiTildeUnitIso _ κ)
      (actualFinitePiTildeUnitIso _ ι).symm _ _
      (actualNormalizedSpecUnitRelationMatrix_tilde j s)
      (actualNormalizedSpecUnitRelationMatrix_tilde j r))

theorem actualNormalizedSpecUnitRelationPairComplex_exact
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (r : κ → ι → A) (s : ι₂ → κ → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hs : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker) (j : Fin 4) :
    (actualNormalizedSpecUnitRelationPairComplex g r s hr hs j).Exact := by
  let S := actualDegreeZeroChartRelationPair_tildeComplex g r s hr hs j
  let T := actualNormalizedSpecUnitRelationPairComplex g r s hr hs j
  let e₁ := actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) ι₂
  let e₂ := actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) κ
  let e₃ := actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) ι
  have hf : e₁.hom ≫ S.f ≫ e₂.inv = T.f := actualNormalizedSpecUnitRelationMatrix_tilde j s
  have hg : e₂.hom ≫ S.g ≫ e₃.inv = T.g := actualNormalizedSpecUnitRelationMatrix_tilde j r
  let E : T ≅ S := ShortComplex.isoMk e₁ e₂ e₃
    ((e₂.comp_inv_eq).mp hf) ((e₃.comp_inv_eq).mp hg)
  exact ShortComplex.exact_of_iso E.symm (actualDegreeZeroChartRelationPair_tildeComplex_exact g r s hr hs j)

end PfaffianDescent.Coray
