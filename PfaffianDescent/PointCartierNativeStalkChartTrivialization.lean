import PfaffianDescent.VoisinProjectiveSpaceCech
import PfaffianDescent.VoisinHypersurfaceTwist
import PfaffianDescent.FiniteProjectiveProjectionFormula

/-! # Native rank-one stalk coordinates on a standard projective chart

These coordinates are the stalk maps of the existing global morphism that
multiplies by a coordinate power and identifies the zero twist with the
structure sheaf. Their invertibility follows from coordinate nonvanishing.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

universe u

variable (K : Type u) [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

theorem pointCartierNativeStalkTrivialization_isIso
    (i : Fin 4) (m : ℕ) (x : Proj PS)
    (hx : (X i : MvPolynomial (Fin 4) K) ∉ x.asHomogeneousIdeal.toIdeal) :
    IsIso ((schemeModuleStalkModuleFunctor (Proj PS) x).map
      (negativeTwistTrivializationHom K i m)) := by
  let U := p3StandardOpen (K := K) i
  have hxU : x ∈ U := (ProjectiveSpectrum.mem_basicOpen PS (X i) x).mpr hx
  let xU : U := ⟨x, hxU⟩
  let F := Scheme.Modules.restrictFunctor U.ι
  have hcomp : IsIso (F.map (negativeTwistTrivializationHom K i m) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) := by
    rw [← p3NegativeTwistOpenIsoUnit_hom K U i le_rfl m]
    infer_instance
  letI := hcomp
  letI : IsIso (F.map (negativeTwistTrivializationHom K i m)) :=
    IsIso.of_isIso_comp_right (F.map (negativeTwistTrivializationHom K i m))
      (Scheme.Modules.restrictUnitIso U.ι).hom
  exact schemeModuleStalkMap_isIso_of_restrict U xU (negativeTwistTrivializationHom K i m)

/-- Actual ambient stalk coordinates for a negative twist on `D₊(Xᵢ)`. -/
def pointCartierNativeStalkTwistIso
    (i : Fin 4) (m : ℕ) (x : Proj PS)
    (hx : (X i : MvPolynomial (Fin 4) K) ∉ x.asHomogeneousIdeal.toIdeal) :
    (schemeModuleStalkModuleFunctor (Proj PS) x).obj (sheafOfModules PS m) ≅
      ModuleCat.of ((Proj PS).presheaf.stalk x) ((Proj PS).presheaf.stalk x) := by
  letI := pointCartierNativeStalkTrivialization_isIso K i m x hx
  exact asIso ((schemeModuleStalkModuleFunctor (Proj PS) x).map
    (negativeTwistTrivializationHom K i m)) ≪≫ schemeModuleUnitStalkIso (Proj PS) x

end PfaffianDescent.ProjectiveNegativeTwist
