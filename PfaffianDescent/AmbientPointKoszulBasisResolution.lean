import PfaffianDescent.AmbientPointKoszulBasisSheafExactness
import PfaffianDescent.AmbientPointKoszulBasisAugmentedExactness
import PfaffianDescent.PointGlobalTraceP3BasisFirstMono
import PfaffianDescent.PointGlobalTraceP3BasisResolution

/-! # The actual unconditional Koszul resolution of every invertible-basis point -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basis_first_mono
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    Mono (pointGlobalTraceP3BasisKoszulFirst K (ambientPointKoszul_basis M)) := by
  apply pointGlobalTraceP3Basis_first_mono
  intro hz
  apply (X_ne_zero (1 : Fin 4) : (X (1 : Fin 4) : MvPolynomial (Fin 4) K) ≠ 0)
  apply (linearSubstitutionEquiv M hM).injective
  exact hz.trans (map_zero (linearSubstitutionEquiv M hM)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual basis-point Koszul resolution has the original native
negative twists and the literal closed-immersion point augmentation.
Its exactness has no remaining geometric premises. -/
def ambientPointKoszul_basisResolution
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    ThreeStepResolution (Proj PS).Modules := by
  letI := ambientPointKoszul_basis_first_mono M hM
  exact pointGlobalTraceP3BasisResolution K (ambientPointKoszul_basis M)
    (ambientPointKoszul_basisPointModule M hM) (ambientPointKoszul_basisAugmentation M hM)
    (ambientPointKoszul_basis_firstMiddle_exact M hM)
    (ambientPointKoszul_basis_middleLast_exact M hM)
    (ambientPointKoszul_basisLast_augmentation_zero M hM)
    (ambientPointKoszul_basisLastAugmentation_exact M hM)

@[simp] theorem ambientPointKoszul_basisResolution_p₀
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (ambientPointKoszul_basisResolution M hM).p₀ = ambientPointKoszul_basisAugmentation M hM := rfl

@[simp] theorem ambientPointKoszul_basisResolution_C₀
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (ambientPointKoszul_basisResolution M hM).C₀ = SheafOfModules.unit (Proj PS).ringCatSheaf := rfl

@[simp] theorem ambientPointKoszul_basisResolution_C₁
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (ambientPointKoszul_basisResolution M hM).C₁ = ⨁ pointGlobalTraceP3CoordinateTriple K 1 := rfl

@[simp] theorem ambientPointKoszul_basisResolution_C₂
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (ambientPointKoszul_basisResolution M hM).C₂ = ⨁ pointGlobalTraceP3CoordinateTriple K 2 := rfl

@[simp] theorem ambientPointKoszul_basisResolution_K₂
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (ambientPointKoszul_basisResolution M hM).K₂ = sheafOfModules PS 3 := rfl

@[simp] theorem ambientPointKoszul_basisResolution_P
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    (ambientPointKoszul_basisResolution M hM).P = ambientPointKoszul_basisPointModule M hM := rfl

end PfaffianDescent.ProjectiveNegativeTwist
