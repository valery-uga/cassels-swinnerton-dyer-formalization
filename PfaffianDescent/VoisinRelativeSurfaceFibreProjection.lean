import PfaffianDescent.VoisinRelativeRingFibreConcrete
import AllCharacteristics.HypersurfaceCoefficientNaturality

/-!
# Projection of a fixed cubic surface fibre to the ground-field surface

The actual fibre isomorphism preserves the surface point itself, not only
its image in ambient projective space. This is the map needed to compare
successive coefficient specializations.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

variable {K T : Type u} [Field K] [CommRing T]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (b : K →+* T) (s : Spec (.of T) ⟶ E)
  (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))

set_option backward.isDefEq.respectTransparency false in
theorem fixedCubicSurfaceFamilyRingFibreIso_toGroundSurface :
    (fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs).hom ≫
      projectiveCoefficientMap b (equationIdeal a ha)
        (equationIdeal (a.map b) (ha.map b))
        (equationIdeal_map b a ha) =
    pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      pullback.fst (hypersurfaceToBase a ha) k := by
  haveI : Mono (hypersurfaceToAmbient a ha) := by infer_instance
  apply (cancel_mono (hypersurfaceToAmbient a ha)).mp
  change ((fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs).hom ≫
      projectiveCoefficientMap b (equationIdeal a ha)
        (equationIdeal (a.map b) (ha.map b))
        (equationIdeal_map b a ha)) ≫
        quotientProjMap (equationIdeal a ha) =
    (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      pullback.fst (hypersurfaceToBase a ha) k) ≫
        quotientProjMap (equationIdeal a ha)
  rw [Category.assoc,
    projectiveCoefficientMap_comp_quotientProjMap b
      (equationIdeal a ha) (equationIdeal (a.map b) (ha.map b))
      (equationIdeal_map b a ha)]
  exact fixedCubicSurfaceFamilyRingFibreIso_toAmbient a ha k b s hs

end PfaffianDescent
