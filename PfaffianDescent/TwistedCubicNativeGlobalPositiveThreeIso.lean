import PfaffianDescent.TwistedCubicOriginalPowerWholeCompatibility
import PfaffianDescent.ActualAmbientPositiveTwistQuotientIso

/-! SOURCE ONLY. GENUINE global native O(1) pullback = O_P1(3) under the
SAME original standard twisted-cubic parametrization. Original two-chart
basis maps, whole overlap agreement and coverage are internally derived. -/
noncomputable section
set_option quotPrecheck false
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open BundleSectionZeroLocus SchemeModuleInternalHom
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "M" => (Scheme.Modules.pullback
  (standardProjectiveLineToTwistedCubic (K := K))).obj (positiveSheafOfModules (grading I) 1)
local notation "N" => positiveSheafOfModules (grading L) 3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original two coordinate opens cover, with lifted index
universe preserving arbitrary original coefficient-field universes. -/
theorem standardProjectiveLineOriginalPowerOpen_cover :
    (⨆ b : ULift.{u} Bool, quotientCoordinateOpen L b.down) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨b, y, hy⟩ := exists_coordinate_chart L x
  apply Opens.mem_iSup.mpr
  refine ⟨⟨b⟩, ?_⟩
  change x ∈ Proj.basicOpen (grading L) (coordinate L b)
  rw [← chartι_opensRange L b]
  exact Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩

/-- Global ORIGINAL native curve O(1) pullback is the ORIGINAL native
O_P1(3), under the SAME actual standard parametrization, with no frame,
transition, compatibility, degree or desired Iso premise. -/
def standardTwistedCubicNativePositiveOnePullbackIso : M ≅ N :=
  schemeModuleIsoGlueOfActualCompatibleOverIsos M N
    (fun b : ULift.{u} Bool => quotientCoordinateOpen L b.down)
    (standardProjectiveLineOriginalPowerOpen_cover (K := K))
    (fun b => standardTwistedCubicOriginalPowerBasisOverIso (K := K) b.down)
    (fun b c => standardTwistedCubicOriginalPowerBasisOverIso_compatible b.down c.down)

/-- Literal manuscript bundle assertion: actual ambient O(1) pulls back
by the ORIGINAL twisted-cubic parametrization to original native O_P1(3).
All construction data are derived under only the original field assumption. -/
def standardTwistedCubicNativeAmbientPositiveOnePullbackIso :
    (Scheme.Modules.pullback
      (standardProjectiveLineToTwistedCubic (K := K) ≫ quotientProjMap I)).obj
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 1) ≅
    positiveSheafOfModules (grading L) 3 :=
  (Scheme.Modules.pullbackComp (standardProjectiveLineToTwistedCubic (K := K))
    (quotientProjMap I)).symm.app
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 1) ≪≫
    (Scheme.Modules.pullback (standardProjectiveLineToTwistedCubic (K := K))).mapIso
      (actualAmbientPositiveTwistQuotientIso I 1) ≪≫
    standardTwistedCubicNativePositiveOnePullbackIso (K := K)

end PfaffianDescent.QuarticNet
