import PfaffianDescent.VoisinRelativeUniversalDivisor
import AllCharacteristics.PullbackRestriction

/-!
# Canonical restriction maps of fixed cubic surface fibres

For a ring-valued parameter point and a further coefficient-ring map, the
surface-family fibres are related by the actual Cartesian restriction map.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics

universe u

variable {K T U : Type u} [Field K] [CommRing T] [CommRing U]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (s : Spec (.of T) ⟶ E) (g : T →+* U)

/-- The canonical map from the fixed surface fibre after a further ring
change to the original fixed surface fibre. -/
noncomputable def fixedCubicSurfaceFamilyFibreRestriction :
    pullback (pullback.snd (hypersurfaceToBase a ha) k)
      (Spec.map (CommRingCat.ofHom g) ≫ s) ⟶
      pullback (pullback.snd (hypersurfaceToBase a ha) k) s :=
  pullbackRestriction
    (pullback.snd (hypersurfaceToBase a ha) k)
    s (Spec.map (CommRingCat.ofHom g) ≫ s)
    (Spec.map (CommRingCat.ofHom g)) rfl

theorem fixedCubicSurfaceFamilyFibreRestriction_fst :
    fixedCubicSurfaceFamilyFibreRestriction a ha k s g ≫
      pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s =
    pullback.fst (pullback.snd (hypersurfaceToBase a ha) k)
      (Spec.map (CommRingCat.ofHom g) ≫ s) :=
  pullbackRestriction_fst _ _ _ _ _

theorem fixedCubicSurfaceFamilyFibreRestriction_snd :
    fixedCubicSurfaceFamilyFibreRestriction a ha k s g ≫
      pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s =
    pullback.snd (pullback.snd (hypersurfaceToBase a ha) k)
      (Spec.map (CommRingCat.ofHom g) ≫ s) ≫
        Spec.map (CommRingCat.ofHom g) :=
  pullbackRestriction_snd _ _ _ _ _

/-- The further fibre restriction is a Cartesian base change along the
coefficient-spectrum map. -/
theorem isPullback_fixedCubicSurfaceFamilyFibreRestriction :
    IsPullback
      (fixedCubicSurfaceFamilyFibreRestriction a ha k s g)
      (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k)
        (Spec.map (CommRingCat.ofHom g) ≫ s))
      (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s)
      (Spec.map (CommRingCat.ofHom g)) :=
  isPullback_pullbackRestriction _ _ _ _ _

end PfaffianDescent
