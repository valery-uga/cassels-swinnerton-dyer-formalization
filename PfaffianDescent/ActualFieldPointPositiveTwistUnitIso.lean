import PfaffianDescent.ActualPositiveTwistPullbackTensorIso
import PfaffianDescent.LocalExtResidueInjective
import Mathlib.RingTheory.KrullDimension.Zero

/- SOURCE ONLY / UNVERIFIED. ONE genuine chart generator trivializes the
positive twist at the SAME actual field-valued point, internally derived. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem actualFieldPointPositiveTwist_exists_pullback_generator
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Spec (CommRingCat.of L) ⟶ scheme I) (m : ℕ) :
    ∃ g : SheafOfModules.unit (scheme I).ringCatSheaf ⟶ positiveSheafOfModules (grading I) m,
      IsIso ((Scheme.Modules.pullback q).map g) := by
  let x₀ : Spec (CommRingCat.of L) := (⊥ : PrimeSpectrum L)
  obtain ⟨U, g, hx₀, hg⟩ := actualPositiveTwist_exists_generator I m (q x₀)
  letI := hg
  refine ⟨g, ?_⟩
  apply schemeModuleMap_isIso_of_stalk
  intro x
  let V := q ⁻¹ᵁ U
  have hx : q x ∈ U := by
    have he : x = x₀ := Subsingleton.elim _ _
    simpa only [he] using hx₀
  let xv : V := ⟨x, hx⟩
  letI : IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.pullback q).map g)) :=
    cubicClosedPointSerreTensorStalk_restrict_pullbackMap_isIso q U V le_rfl g
  exact cubicClosedPointSerreTensorStalk_map_isIso_of_restrict V xv
    ((Scheme.Modules.pullback q).map g)

def actualFieldPointPositiveTwistUnitIso
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Spec (CommRingCat.of L) ⟶ scheme I) (m : ℕ) :
    (Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) m) ≅
      SheafOfModules.unit (Spec (CommRingCat.of L)).ringCatSheaf := by
  let h := actualFieldPointPositiveTwist_exists_pullback_generator I q m
  let g := Classical.choose h
  letI : IsIso ((Scheme.Modules.pullback q).map g) := Classical.choose_spec h
  letI : IsIso (pullbackUnitComparison q) := isIso_pullbackUnitComparison q
  exact (asIso ((Scheme.Modules.pullback q).map g)).symm ≪≫
    asIso (pullbackUnitComparison q)

/-- Genuine tensor untwisting at SAME q; no trivialization certificate input. -/
def actualFieldPointPositiveTwistTensorUntwistIso
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Spec (CommRingCat.of L) ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ) :
    (Scheme.Modules.pullback q).obj (schemeModuleTensor M (positiveSheafOfModules (grading I) m)) ≅
      (Scheme.Modules.pullback q).obj M :=
  actualPositiveTwistPullbackTensorIso I q M m ≪≫
    schemeModuleTensorMapIso (Iso.refl ((Scheme.Modules.pullback q).obj M))
      (actualFieldPointPositiveTwistUnitIso I q m) ≪≫
    schemeModuleTensorUnitRightIso ((Scheme.Modules.pullback q).obj M)

end PfaffianDescent
