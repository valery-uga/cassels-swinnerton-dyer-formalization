import PfaffianDescent.PointGlobalTraceP3BasisBiproductStalk
import PfaffianDescent.AmbientPointKoszulBasisStalkExactness
import PfaffianDescent.VoisinProjectiveSpaceCech

/-! # Global exactness of the actual invertible-basis Koszul differential pairs -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)

local instance ambientPointKoszul_basisSheafPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- The actual first/middle pair as a short complex. -/
def ambientPointKoszul_basis_firstMiddleShortComplex : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (pointGlobalTraceP3BasisKoszulFirst K (ambientPointKoszul_basis M))
    (pointGlobalTraceP3BasisKoszulMiddle K (ambientPointKoszul_basis M))
    (pointGlobalTraceP3BasisKoszul_first_middle_zero K (ambientPointKoszul_basis M))

/-- The actual middle/last pair into the zero twist as a short complex. -/
def ambientPointKoszul_basis_middleLastZeroShortComplex : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (pointGlobalTraceP3BasisKoszulMiddle K (ambientPointKoszul_basis M))
    (pointGlobalTraceP3BasisKoszulLastZeroTwist K (ambientPointKoszul_basis M))
    (pointGlobalTraceP3BasisKoszul_middle_lastZeroTwist_zero K (ambientPointKoszul_basis M))

/-- The actual middle/last pair into the structure sheaf as a short complex. -/
def ambientPointKoszul_basis_middleLastShortComplex : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (pointGlobalTraceP3BasisKoszulMiddle K (ambientPointKoszul_basis M))
    (pointGlobalTraceP3BasisKoszulLast K (ambientPointKoszul_basis M))
    (pointGlobalTraceP3BasisKoszul_middle_last_zero K (ambientPointKoszul_basis M))

include hM

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the first two actual categorical sheaf stalk maps. -/
theorem ambientPointKoszul_basis_firstMiddle_stalk_exact
    (j : Fin 4) (x : Proj PS) (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulFirst K (ambientPointKoszul_basis M)))
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulMiddle K (ambientPointKoszul_basis M))) := by
  have hlocal := LinearMap.exact_iff.mpr (ambientPointKoszul_basisStalk_exact_middle M hM j x hx).symm
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := pointGlobalTraceP3Basis_stalkCoordinate K (ambientPointKoszul_basis M) j x hx 3)
    (e₂ := pointGlobalTraceP3Basis_stalkTripleCoordinate K (ambientPointKoszul_basis M) j x hx 2)
    (e₃ := pointGlobalTraceP3Basis_stalkTripleCoordinate K (ambientPointKoszul_basis M) j x hx 1)
    (g₁₂ := (threeGeneratorFirst
      (ambientPointKoszul_basisStalkParameter M 1 j x hx)
      (ambientPointKoszul_basisStalkParameter M 2 j x hx)
      (ambientPointKoszul_basisStalkParameter M 3 j x hx)).toAddMonoidHom)
    (g₂₃ := (threeGeneratorMiddle
      (ambientPointKoszul_basisStalkParameter M 1 j x hx)
      (ambientPointKoszul_basisStalkParameter M 2 j x hx)
      (ambientPointKoszul_basisStalkParameter M 3 j x hx)).toAddMonoidHom)
    (H := hlocal)
  · apply AddMonoidHom.ext
    intro z
    exact (pointGlobalTraceP3Basis_first_stalk_coordinates K (ambientPointKoszul_basis M) j x hx z).symm
  · apply AddMonoidHom.ext
    intro z
    exact (pointGlobalTraceP3Basis_middle_stalk_coordinates K (ambientPointKoszul_basis M) j x hx z).symm

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the last two actual categorical sheaf stalk maps into the zero twist. -/
theorem ambientPointKoszul_basis_middleLastZero_stalk_exact
    (j : Fin 4) (x : Proj PS) (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulMiddle K (ambientPointKoszul_basis M)))
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulLastZeroTwist K (ambientPointKoszul_basis M))) := by
  have hlocal := LinearMap.exact_iff.mpr (ambientPointKoszul_basisStalk_exact_last M hM j x hx).symm
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := pointGlobalTraceP3Basis_stalkTripleCoordinate K (ambientPointKoszul_basis M) j x hx 2)
    (e₂ := pointGlobalTraceP3Basis_stalkTripleCoordinate K (ambientPointKoszul_basis M) j x hx 1)
    (e₃ := pointGlobalTraceP3Basis_stalkCoordinate K (ambientPointKoszul_basis M) j x hx 0)
    (g₁₂ := (threeGeneratorMiddle
      (ambientPointKoszul_basisStalkParameter M 1 j x hx)
      (ambientPointKoszul_basisStalkParameter M 2 j x hx)
      (ambientPointKoszul_basisStalkParameter M 3 j x hx)).toAddMonoidHom)
    (g₂₃ := (threeGeneratorLast
      (ambientPointKoszul_basisStalkParameter M 1 j x hx)
      (ambientPointKoszul_basisStalkParameter M 2 j x hx)
      (ambientPointKoszul_basisStalkParameter M 3 j x hx)).toAddMonoidHom)
    (H := hlocal)
  · apply AddMonoidHom.ext
    intro z
    exact (pointGlobalTraceP3Basis_middle_stalk_coordinates K (ambientPointKoszul_basis M) j x hx z).symm
  · apply AddMonoidHom.ext
    intro z
    exact (pointGlobalTraceP3Basis_last_stalk_coordinates K (ambientPointKoszul_basis M) j x hx z).symm

private theorem basisChart_exists (x : Proj PS) :
    ∃ j : Fin 4, (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl := by
  have hx : x ∈ ⨆ i : Fin 4, Proj.basicOpen PS (ambientPointKoszul_basis M i).val := by
    rw [ambientPointKoszul_basisOpen_iSup M hM]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨j, hj⟩

set_option backward.isDefEq.respectTransparency false in
/-- Global exactness at the actual rank-three negative-two term. -/
theorem ambientPointKoszul_basis_firstMiddle_exact :
    (ambientPointKoszul_basis_firstMiddleShortComplex M).Exact := by
  let S := ambientPointKoszul_basis_firstMiddleShortComplex M
  let T := SheafOfModules.toSheaf.{u} (Proj PS).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj PS) x)).Exact
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  obtain ⟨j, hj⟩ := basisChart_exists M hM x
  exact ambientPointKoszul_basis_firstMiddle_stalk_exact M hM j x hj

set_option backward.isDefEq.respectTransparency false in
/-- Global exactness at the actual rank-three negative-one term. -/
theorem ambientPointKoszul_basis_middleLastZero_exact :
    (ambientPointKoszul_basis_middleLastZeroShortComplex M).Exact := by
  let S := ambientPointKoszul_basis_middleLastZeroShortComplex M
  let T := SheafOfModules.toSheaf.{u} (Proj PS).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj PS) x)).Exact
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  obtain ⟨j, hj⟩ := basisChart_exists M hM x
  exact ambientPointKoszul_basis_middleLastZero_stalk_exact M hM j x hj

set_option backward.isDefEq.respectTransparency false in
/-- Global exactness at the negative-one term with the actual structure-sheaf target. -/
theorem ambientPointKoszul_basis_middleLast_exact :
    (ambientPointKoszul_basis_middleLastShortComplex M).Exact := by
  let e : ambientPointKoszul_basis_middleLastZeroShortComplex M ≅
      ambientPointKoszul_basis_middleLastShortComplex M :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (unitIsoZeroTwist PS).symm
      (by simp [ambientPointKoszul_basis_middleLastZeroShortComplex, ambientPointKoszul_basis_middleLastShortComplex])
      (by simp [ambientPointKoszul_basis_middleLastZeroShortComplex, ambientPointKoszul_basis_middleLastShortComplex,
        pointGlobalTraceP3BasisKoszulLast])
  exact ShortComplex.exact_of_iso e (ambientPointKoszul_basis_middleLastZero_exact M hM)

end PfaffianDescent.ProjectiveNegativeTwist
