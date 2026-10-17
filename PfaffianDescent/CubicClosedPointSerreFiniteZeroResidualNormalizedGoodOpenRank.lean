import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedGluedGoodOpenFlat
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualProjectiveLineIrreducible
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_goodOpen_rank
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ projectiveLineProj K) [IsProper f]
    [Flat (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f)]
    (y₀ y₁ : projectiveLineProj K)
    (h₀ : (f ⁻¹' {y₀}).Finite) (h₁ : (f ⁻¹' {y₁}).Finite) :
    (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f).finrank
      ⟨y₀, cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre f y₀ h₀⟩ =
    (f ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen f).finrank
      ⟨y₁, cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre f y₁ h₁⟩ := by
  let V := cubicClosedPointSerreFiniteZeroResidual_goodOpen f
  letI := cubicClosedPointSerreFiniteZeroResidual_projectiveLine_preirreducible K
  letI : PreirreducibleSpace V := V.ι.isOpenEmbedding.preirreducibleSpace
  letI : Nonempty V := ⟨⟨y₀,
    cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre f y₀ h₀⟩⟩
  letI : IsLocallyNoetherian (projectiveLineProj K) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveLineProjToBase K)
  letI : IsFinite (f ∣_ V) := cubicClosedPointSerreFiniteZeroResidual_goodOpen_finite f
  exact (Scheme.Hom.isLocallyConstant_finrank (f ∣_ V)).apply_eq_of_preconnectedSpace _ _

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedGluedGoodOpen_rank
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    letI := SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine
      (hypersurfaceToBase p hp) C seed
    let g := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      (hypersurfaceToBase p hp) C seed ≫ projectiveLineAmbientToLine K (hypersurfaceToBase p hp)
    ∀ (y₀ y₁ : projectiveLineProj K)
      (h₀ : (g ⁻¹' {y₀}).Finite) (h₁ : (g ⁻¹' {y₁}).Finite),
    (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g).finrank
      ⟨y₀, cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y₀ h₀⟩ =
    (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g).finrank
      ⟨y₁, cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y₁ h₁⟩ := by
  letI := SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine
    (hypersurfaceToBase p hp) C seed
  let g := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
    (hypersurfaceToBase p hp) C seed ≫ projectiveLineAmbientToLine K (hypersurfaceToBase p hp)
  letI : Flat (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g) :=
    cubicClosedPointSerreFiniteZeroResidual_normalizedGluedGoodOpen_flat p hp hp0 C seed
  exact cubicClosedPointSerreFiniteZeroResidual_projectiveLine_goodOpen_rank g

end PfaffianDescent
