import PfaffianDescent.VoisinRelativeSurfaceFibreNaturality
import PfaffianDescent.ProjectiveCoefficientIdealMap

/-!
# Coefficient-changed cubic ideals and the explicit surface fibres

The homogeneous ideal used by the universal ideal-base-change theorem is
the defining ideal of the cubic obtained by successive coefficient change.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K T U : Type u} [Field K] [CommRing T] [CommRing U]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  (b : K →+* T) (g : T →+* U)

/-- The coefficient-extended equation ideal is the actual ideal of the
successively specialized cubic, as a homogeneous ideal. -/
theorem coefficientChangedHomogeneousIdeal_equationIdeal_map_comp :
    coefficientChangedHomogeneousIdeal g (equationIdeal (a.map b) (ha.map b)) =
      equationIdeal (a.map (g.comp b)) (ha.map (g.comp b)) := by
  apply HomogeneousIdeal.ext
  rw [← coefficientChangedHomogeneousIdeal_toIdeal g
    (equationIdeal (a.map b) (ha.map b))]
  exact equationIdeal_map_comp b g a ha

/-- The projective coefficient map used by ideal base change is the
hypersurface restriction after identifying its defining ideal. -/
theorem coefficientChangedSurfaceMap_eq_hypersurfaceRestriction :
    let J := equationIdeal (a.map b) (ha.map b)
    let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
    eqToHom (congrArg scheme hJ) ≫
        hypersurfaceCoefficientRestriction b g a ha =
      projectiveCoefficientMap g J (coefficientChangedHomogeneousIdeal g J)
        (coefficientChangedHomogeneousIdeal_toIdeal g J) := by
  let J := equationIdeal (a.map b) (ha.map b)
  let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
  have H := projectiveCoefficientMap_transport g J J
    (coefficientChangedHomogeneousIdeal g J)
    (equationIdeal (a.map (g.comp b)) (ha.map (g.comp b)))
    (coefficientChangedHomogeneousIdeal_toIdeal g J)
    (equationIdeal_map_comp b g a ha) rfl hJ
  change eqToHom (congrArg scheme hJ) ≫
      projectiveCoefficientMap g J
        (equationIdeal (a.map (g.comp b)) (ha.map (g.comp b)))
        (equationIdeal_map_comp b g a ha) =
      projectiveCoefficientMap g J (coefficientChangedHomogeneousIdeal g J)
        (coefficientChangedHomogeneousIdeal_toIdeal g J)
  simpa only [eqToHom_refl, Category.comp_id] using H

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient map appearing in universal ideal base change is the
canonical restriction of the constant cubic surface family, after the
defining-ideal identification on its source. -/
theorem coefficientChangedSurfaceMap_toFamilyFibre_naturality
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b)) :
    let J := equationIdeal (a.map b) (ha.map b)
    let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
    let sg := Spec.map (CommRingCat.ofHom g) ≫ s
    let hsg := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
    let eT := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
    let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b) sg hsg
    projectiveCoefficientMap g J (coefficientChangedHomogeneousIdeal g J)
        (coefficientChangedHomogeneousIdeal_toIdeal g J) ≫ eT.inv =
      (eqToHom (congrArg scheme hJ) ≫ eU.inv) ≫
        fixedCubicSurfaceFamilyFibreRestriction a ha k s g := by
  let J := equationIdeal (a.map b) (ha.map b)
  let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
  let sg := Spec.map (CommRingCat.ofHom g) ≫ s
  let hsg := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
  let eT := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
  let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b) sg hsg
  let cJ := projectiveCoefficientMap g J (coefficientChangedHomogeneousIdeal g J)
    (coefficientChangedHomogeneousIdeal_toIdeal g J)
  have hm := coefficientChangedSurfaceMap_eq_hypersurfaceRestriction a ha b g
  have hn := fixedCubicSurfaceFamilyFieldFibreIso_naturality a ha k b s hs g
  calc
    cJ ≫ eT.inv =
        (eqToHom (congrArg scheme hJ) ≫
          hypersurfaceCoefficientRestriction b g a ha) ≫ eT.inv := by
            exact congrArg (fun m => m ≫ eT.inv) hm.symm
    _ = (eqToHom (congrArg scheme hJ) ≫ eU.inv) ≫
        fixedCubicSurfaceFamilyFibreRestriction a ha k s g := by
          simp only [Category.assoc]
          exact congrArg (fun m => eqToHom (congrArg scheme hJ) ≫ m) hn

end PfaffianDescent
