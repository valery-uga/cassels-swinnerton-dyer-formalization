import PfaffianDescent.PointCartierNativeStalkActualRestriction
import PfaffianDescent.PointCartierNativeStalkRingQuotient
import PfaffianDescent.PointCartierNativeStalkPushforwardExt
import PfaffianDescent.PointCartierNativeStalkBoundaryDetection
import PfaffianDescent.PointCartierNativeStalkRegularPairTransfer
import PfaffianDescent.PointCartierNativeStalkSurfaceRestriction
import PfaffianDescent.FieldPointExtResiduePresentation

/-! # Nonvanishing of the actual cubic Cartier boundary from a native residue class

All ring, pushforward-stalk, and Cartier-sequence comparisons are constructed.
The only local point data are a regular pair and its actual endpoint isomorphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective MvPolynomial
open scoped nonZeroDivisors

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

theorem pointCartierNativeStalkHypersurfacePrincipalData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (y : hypersurface p hp) (j : Fin 4)
    (hx : X j ∉ (hypersurfaceAmbientPoint p hp y).asHomogeneousIdeal.toIdeal) :
    ∃ t : (Proj PS).presheaf.stalk (hypersurfaceAmbientPoint p hp y),
      t ∈ ((Proj PS).presheaf.stalk (hypersurfaceAmbientPoint p hp y))⁰ ∧
      ∃ e : (((Proj PS).presheaf.stalk (hypersurfaceAmbientPoint p hp y)) ⧸
          Ideal.span {t}) ≃+* (hypersurface p hp).presheaf.stalk y,
        ((hypersurfaceToAmbient p hp).stalkMap y).hom =
          e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})) := by
  refine ⟨pointCartierNativeStalkHypersurfaceScalar p hp j _ hx,
    pointCartierNativeStalkHypersurfaceScalar_regular p hp hp0 j _ hx,
    pointCartierNativeStalkSurfaceRingEquiv p hp j y hx, ?_⟩
  ext r
  exact (pointCartierNativeStalkSurfaceRingEquiv_mk p hp j y hx r).symm

theorem pointCartierNativeStalkHypersurface_boundary_ne_zero_of_local
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExtSurface : HasExt.{u} (hypersurface p hp).Modules]
    [EnoughInjectives (hypersurface p hp).Modules]
    (y : hypersurface p hp) (j : Fin 4)
    (hx : X j ∉ (hypersurfaceAmbientPoint p hp y).asHomogeneousIdeal.toIdeal)
    [hExtLocalAmbient : HasExt.{u + 1}
      (ModuleCat.{u} ((Proj PS).presheaf.stalk (hypersurfaceAmbientPoint p hp y)))]
    [hExtLocalSurface : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk y))]
    (M : (hypersurface p hp).Modules)
    (f g : (hypersurface p hp).presheaf.stalk y)
    (hf : f ∈ ((hypersurface p hp).presheaf.stalk y)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      (((hypersurface p hp).presheaf.stalk y) ⧸ Ideal.span {f})⁰)
    (qM : (schemeModuleStalkModuleFunctor (hypersurface p hp) y).obj M ≅
      ModuleCat.of ((hypersurface p hp).presheaf.stalk y)
        (((hypersurface p hp).presheaf.stalk y) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor (hypersurface p hp) y).obj
      (sheafOfModules (grading (equationIdeal p hp)) 1) ≅
        ModuleCat.of ((hypersurface p hp).presheaf.stalk y)
          ((hypersurface p hp).presheaf.stalk y))
    (z : Ext.{u} M (sheafOfModules (grading (equationIdeal p hp)) 1) 2)
    (hlocal : schemeModuleStalkModuleExtMap (hypersurface p hp) y _ _ 2 z ≠ 0) :
    (z.mapExactFunctor (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))).comp
      (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass rfl ≠ 0 := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExtAmbient
  letI : HasExt.{u} (SheafOfModules.{u} (hypersurface p hp).ringCatSheaf) := hExtSurface
  let x := hypersurfaceAmbientPoint p hp y
  let A := (Proj PS).presheaf.stalk x
  let B := (hypersurface p hp).presheaf.stalk y
  letI : HasExt.{u + 1} (ModuleCat.{u} A) := hExtLocalAmbient
  letI : HasExt.{u + 1} (ModuleCat.{u} B) := hExtLocalSurface
  letI : HasExt.{u + 1} (ModuleCat.{u}
      ((Proj PS).presheaf.stalk ((hypersurfaceToAmbient p hp) y))) := hExtLocalAmbient
  let φ : A →+* B := ((hypersurfaceToAmbient p hp).stalkMap y).hom
  obtain ⟨t, ht, e, hφ⟩ := pointCartierNativeStalkHypersurfacePrincipalData p hp hp0 y j hx
  let P : (hypersurface p hp).Modules ⥤ (Proj PS).Modules :=
    Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)
  letI : PreservesFiniteLimits P := by
    change PreservesFiniteLimits (SheafOfModules.pushforward _)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  let F : ModuleCat.{u} B ⥤ ModuleCat.{u} A := ModuleCat.restrictScalars φ
  let L : (Proj PS).Modules ⥤ ModuleCat.{u} A := schemeModuleStalkModuleFunctor (Proj PS) x
  let LS : (hypersurface p hp).Modules ⥤ ModuleCat.{u} B :=
    schemeModuleStalkModuleFunctor (hypersurface p hp) y
  let N : (hypersurface p hp).Modules := sheafOfModules (grading (equationIdeal p hp)) 1
  let a : Ext.{u + 1} (L.obj (P.obj M)) (L.obj (P.obj N)) 2 :=
    (z.mapExactFunctor P).mapExactFunctor L
  have ha : a ≠ 0 := by
    apply pointCartierNativeStalkPushforwardExt_nonzero.{u}
      (hExtX := hExtSurface) (hExtY := hExtAmbient)
      (hExtLocalX := hExtLocalSurface) (hExtLocalY := hExtLocalAmbient)
      (hypersurfaceToAmbient p hp) y z
    intro hr
    apply hlocal
    exact (pointCartierNativeStalkSurfaceRestriction_eq_zero_iff
      t e φ hφ ht f g hf hg (LS.obj M) (LS.obj N) qM qN
        (z.mapExactFunctor LS)).mp hr
  letI : Subsingleton (Ext.{u + 1} (F.obj (LS.obj M)) (ModuleCat.of A A) 2) :=
    pointCartierNativeStalkActualAmbientExtTwoPair_subsingleton
      t e φ hφ ht f g hf hg (LS.obj M) qM
  let eM := pointCartierNativeStalkPushforwardIso (hypersurfaceToAmbient p hp)
    (hypersurfaceToAmbient p hp).isClosedEmbedding.isInducing y M
  letI : Subsingleton (Ext.{u + 1} (L.obj (P.obj M)) (ModuleCat.of A A) 2) :=
    (extPrecompIsoOfIso.{u + 1, u, u + 1} (Y := ModuleCat.of A A) (n := 2)
      eM).toEquiv.subsingleton_congr.mpr inferInstance
  letI : Subsingleton (Ext.{u + 1} (L.obj (P.obj M))
      (L.obj (hypersurfaceTwistRestrictionSequence p hp 1).X₂) 2) :=
    ext_subsingleton_of_iso_right.{u + 1, u, u + 1}
      (pointCartierNativeStalkTwistIso K j 1 x hx).symm 2
  exact pointCartierNativeStalkExactBoundary_nonzero.{u + 1, u, u, u + 1, u, u + 1} L
    (hypersurfaceTwistRestrictionSequence p hp 1)
    (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1)
    (P.obj M) (z.mapExactFunctor P) ha

end PfaffianDescent.ProjectiveNegativeTwist
