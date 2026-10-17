import PfaffianDescent.CorayActualDegreeZeroChartPresentation

/-! The actual affine tilde of the OWN normalized Proj-chart presentation.
The ring is the degree-zero chart ring, not the localized affine cone.
SOURCE ONLY UNVERIFIED; root owns compiler and acceptance. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The literal normalized module matrices as a native chart short complex. -/
def actualDegreeZeroChartPresentation_complex
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) : ShortComplex (ModuleCat.{u} (HomogeneousLocalization.Away PS (X j))) :=
  ModuleCat.shortComplexOfCompEqZero
    (actualDegreeZeroChartRelationMap j r) (actualDegreeZeroChartGeneratorMap j g) (by
      apply LinearMap.ext
      intro x
      exact (actualDegreeZeroChartPresentation_exact I g r hg hr j _).mpr ⟨x, rfl⟩)

/-- The actual tilde sheaf complex on Spec of the native degree-zero chart. -/
def actualDegreeZeroChartPresentation_tildeComplex
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) :
    ShortComplex (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules := by
  let F := tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  exact (actualDegreeZeroChartPresentation_complex I g r hg hr j).map F

/-- Exactness is derived through the actual affine tilde functor of the
SAME normalized chart maps. No native sheaf exactness premise is supplied. -/
theorem actualDegreeZeroChartPresentation_tildeComplex_exact
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) : (actualDegreeZeroChartPresentation_tildeComplex I g r hg hr j).Exact := by
  let F := tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  letI : F.PreservesMonomorphisms :=
    PfaffianDescent.tilde_preservesMonomorphisms
      (R := CommRingCat.of (HomogeneousLocalization.Away PS (X j)))
  letI : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  have h : (actualDegreeZeroChartPresentation_complex I g r hg hr j).Exact :=
    ModuleCat.shortComplex_exact _ (actualDegreeZeroChartPresentation_exact I g r hg hr j)
  change ((actualDegreeZeroChartPresentation_complex I g r hg hr j).map F).Exact
  exact h.map F

end PfaffianDescent.Coray
