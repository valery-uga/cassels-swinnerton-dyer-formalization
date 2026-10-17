import PfaffianDescent.PointCartierNativeStalkPrincipalNormalization
import PfaffianDescent.PointCartierNativeStalkChartTrivialization

/-! # The actual cubic Cartier stalk sequence in principal coordinates

The first two endpoint coordinates are actual standard-chart trivializations.
The quotient endpoint and both squares are constructed from exactness.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial
open scoped nonZeroDivisors

universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable [IsDomain (AllCharacteristics.HomogeneousProjective.CoordinateRing
  (AllCharacteristics.HomogeneousProjective.equationIdeal p hp))]
variable (hp0 : p ≠ 0) (i : Fin 4)
variable (x : _root_.ProjectiveSpectrum
  (MvPolynomial.homogeneousSubmodule (Fin 4) K))
variable (hx : (X i : MvPolynomial (Fin 4) K) ∉ x.asHomogeneousIdeal.toIdeal)

def pointCartierNativeStalkHypersurfaceComplex :
    ShortComplex (ModuleCat ((Proj PS).presheaf.stalk x)) :=
  (hypersurfaceTwistRestrictionSequence p hp 1).map
    (schemeModuleStalkModuleFunctor (Proj PS) x)

include hp0 in
theorem pointCartierNativeStalkHypersurfaceComplex_shortExact :
    (pointCartierNativeStalkHypersurfaceComplex p hp x).ShortExact :=
  (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).map_of_exact _

/-- The native local equation, read in the actual chart bases of `O(-4)`
and `O(-1)`. -/
def pointCartierNativeStalkHypersurfaceScalar : (Proj PS).presheaf.stalk x :=
  pointCartierNativeStalkScalar (pointCartierNativeStalkHypersurfaceComplex p hp x)
    (pointCartierNativeStalkTwistIso K i 4 x hx)
    (pointCartierNativeStalkTwistIso K i 1 x hx)

include hp0 in
theorem pointCartierNativeStalkHypersurfaceScalar_regular :
    pointCartierNativeStalkHypersurfaceScalar p hp i x hx ∈
      ((Proj PS).presheaf.stalk x)⁰ :=
  pointCartierNativeStalkScalar_regular _
    (pointCartierNativeStalkHypersurfaceComplex_shortExact p hp hp0 x) _ _

/-- A proved isomorphism of the actual Cartier stalk sequence with the
principal coefficient sequence used by the local Yoneda calculation. -/
def pointCartierNativeStalkHypersurfaceIso :
    pointCartierNativeStalkHypersurfaceComplex p hp x ≅
      pointCartierYonedaCoefficientComplex
        (pointCartierNativeStalkHypersurfaceScalar p hp i x hx) :=
  pointCartierNativeStalkPrincipalIso _
    (pointCartierNativeStalkHypersurfaceComplex_shortExact p hp hp0 x)
    (pointCartierNativeStalkTwistIso K i 4 x hx)
    (pointCartierNativeStalkTwistIso K i 1 x hx)

/-- The actual global Cartier extension class becomes the principal local
extension class under the exact native stalk functor and the constructed
endpoint identifications. No commuting square is assumed. -/
theorem pointCartierNativeStalkHypersurface_extClass
    [hGlobalExt : HasExt.{u} (Proj PS).Modules]
    [hLocalExt : HasExt.{u + 1} (ModuleCat ((Proj PS).presheaf.stalk x))] :
    (schemeModuleStalkModuleExtMap (Proj PS) x _ _ 1
      (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass).comp
        (Ext.mk₀ (pointCartierNativeStalkHypersurfaceIso p hp hp0 i x hx).hom.τ₁)
        (add_zero 1) =
      (Ext.mk₀ (pointCartierNativeStalkHypersurfaceIso p hp hp0 i x hx).hom.τ₃).comp
        (pointCartierYonedaCoefficientComplex_shortExact _
          (pointCartierNativeStalkHypersurfaceScalar_regular p hp hp0 i x hx)).extClass
        (zero_add 1) := by
  rw [schemeModuleStalkModuleExtMap_extClass]
  exact ShortComplex.ShortExact.extClass_naturality _ _
    (pointCartierNativeStalkHypersurfaceIso p hp hp0 i x hx).hom

/-- The actual Cartier Yoneda boundary, in every degree, agrees with the
principal local boundary after taking the actual stalk and applying the
constructed coefficient endpoint coordinates. -/
theorem pointCartierNativeStalkHypersurface_boundary
    [hGlobalExt : HasExt.{u} (Proj PS).Modules]
    [hLocalExt : HasExt.{u + 1} (ModuleCat ((Proj PS).presheaf.stalk x))]
    {M : (Proj PS).Modules} {n : ℕ}
    (z : Ext.{u} M (hypersurfaceTwistRestrictionSequence p hp 1).X₃ n) :
    (schemeModuleStalkModuleExtMap (Proj PS) x _ _ (n + 1)
      (z.comp (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass rfl)).comp
        (Ext.mk₀ (pointCartierNativeStalkHypersurfaceIso p hp hp0 i x hx).hom.τ₁)
        (add_zero (n + 1)) =
      ((schemeModuleStalkModuleExtMap (Proj PS) x _ _ n z).comp
        (Ext.mk₀ (pointCartierNativeStalkHypersurfaceIso p hp hp0 i x hx).hom.τ₃)
        (add_zero n)).comp
        (pointCartierYonedaCoefficientComplex_shortExact _
          (pointCartierNativeStalkHypersurfaceScalar_regular p hp hp0 i x hx)).extClass rfl := by
  rw [schemeModuleStalkModuleExtMap_comp, Ext.comp_assoc_of_third_deg_zero,
    pointCartierNativeStalkHypersurface_extClass,
    ← Ext.comp_assoc_of_second_deg_zero]

end PfaffianDescent.ProjectiveNegativeTwist
