import PfaffianDescent.AmbientPointKoszulBiproductStalk
import PfaffianDescent.VoisinProjectiveSpaceCech

/-! # Global exactness of the actual coordinate Koszul differential pairs -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance ambientPointKoszul_sheafPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- The actual first/middle pair as a short complex. -/
def ambientPointKoszul_firstMiddleShortComplex : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (pointGlobalTraceP3CoordinateKoszulFirst K)
    (pointGlobalTraceP3CoordinateKoszulMiddle K)
    (pointGlobalTraceP3CoordinateKoszul_first_middle_zero K)

/-- The actual middle/last pair into the zero twist as a short complex. -/
def ambientPointKoszul_middleLastZeroShortComplex : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (pointGlobalTraceP3CoordinateKoszulMiddle K)
    (pointGlobalTraceP3CoordinateKoszulLastZeroTwist K)
    (pointGlobalTraceP3CoordinateKoszul_middle_lastZeroTwist_zero K)

/-- The actual middle/last pair into the structure sheaf as a short complex. -/
def ambientPointKoszul_middleLastShortComplex : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (pointGlobalTraceP3CoordinateKoszulMiddle K)
    (pointGlobalTraceP3CoordinateKoszulLast K)
    (pointGlobalTraceP3CoordinateKoszul_middle_last_zero K)

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the first two actual categorical sheaf stalk maps. -/
theorem ambientPointKoszul_firstMiddle_stalk_exact
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulFirst K))
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulMiddle K)) := by
  have hlocal := LinearMap.exact_iff.mpr (ambientPointKoszul_stalk_exact_middle K j x hx).symm
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := ambientPointKoszul_stalkCoordinate K j x hx 3)
    (e₂ := ambientPointKoszul_stalkTripleCoordinate K j x hx 2)
    (e₃ := ambientPointKoszul_stalkTripleCoordinate K j x hx 1)
    (g₁₂ := (threeGeneratorFirst
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)).toAddMonoidHom)
    (g₂₃ := (threeGeneratorMiddle
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)).toAddMonoidHom)
    (H := hlocal)
  · apply AddMonoidHom.ext
    intro z
    exact (ambientPointKoszul_first_stalk_coordinates K j x hx z).symm
  · apply AddMonoidHom.ext
    intro z
    exact (ambientPointKoszul_middle_stalk_coordinates K j x hx z).symm

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the last two actual categorical sheaf stalk maps into the zero twist. -/
theorem ambientPointKoszul_middleLastZero_stalk_exact
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulMiddle K))
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulLastZeroTwist K)) := by
  have hlocal := LinearMap.exact_iff.mpr (ambientPointKoszul_stalk_exact_last K j x hx).symm
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := ambientPointKoszul_stalkTripleCoordinate K j x hx 2)
    (e₂ := ambientPointKoszul_stalkTripleCoordinate K j x hx 1)
    (e₃ := ambientPointKoszul_stalkCoordinate K j x hx 0)
    (g₁₂ := (threeGeneratorMiddle
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)).toAddMonoidHom)
    (g₂₃ := (threeGeneratorLast
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)).toAddMonoidHom)
    (H := hlocal)
  · apply AddMonoidHom.ext
    intro z
    exact (ambientPointKoszul_middle_stalk_coordinates K j x hx z).symm
  · apply AddMonoidHom.ext
    intro z
    exact (ambientPointKoszul_last_stalk_coordinates K j x hx z).symm

private theorem coordinateChart_exists (x : Proj PS) :
    ∃ j : Fin 4, X j ∈ (pointIdeal PS x).primeCompl := by
  have hx : x ∈ ⨆ i : Fin 4, p3StandardOpen (K := K) i := by
    rw [p3StandardOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨j, hj⟩

set_option backward.isDefEq.respectTransparency false in
/-- Global exactness at the actual rank-three negative-two term. -/
theorem ambientPointKoszul_firstMiddle_exact :
    (ambientPointKoszul_firstMiddleShortComplex K).Exact := by
  let S := ambientPointKoszul_firstMiddleShortComplex K
  let T := SheafOfModules.toSheaf.{u} (Proj PS).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj PS) x)).Exact
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  obtain ⟨j, hj⟩ := coordinateChart_exists K x
  exact ambientPointKoszul_firstMiddle_stalk_exact K j x hj

set_option backward.isDefEq.respectTransparency false in
/-- Global exactness at the actual rank-three negative-one term. -/
theorem ambientPointKoszul_middleLastZero_exact :
    (ambientPointKoszul_middleLastZeroShortComplex K).Exact := by
  let S := ambientPointKoszul_middleLastZeroShortComplex K
  let T := SheafOfModules.toSheaf.{u} (Proj PS).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj PS) x)).Exact
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  obtain ⟨j, hj⟩ := coordinateChart_exists K x
  exact ambientPointKoszul_middleLastZero_stalk_exact K j x hj

set_option backward.isDefEq.respectTransparency false in
/-- Global exactness at the negative-one term with the actual structure-sheaf target. -/
theorem ambientPointKoszul_middleLast_exact :
    (ambientPointKoszul_middleLastShortComplex K).Exact := by
  let e : ambientPointKoszul_middleLastZeroShortComplex K ≅
      ambientPointKoszul_middleLastShortComplex K :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (unitIsoZeroTwist PS).symm
      (by simp [ambientPointKoszul_middleLastZeroShortComplex, ambientPointKoszul_middleLastShortComplex])
      (by simp [ambientPointKoszul_middleLastZeroShortComplex, ambientPointKoszul_middleLastShortComplex,
        pointGlobalTraceP3CoordinateKoszulLast])
  exact ShortComplex.exact_of_iso e (ambientPointKoszul_middleLastZero_exact K)

end PfaffianDescent.ProjectiveNegativeTwist
