import PfaffianDescent.VoisinRelativeSurfaceFibreRestriction
import PfaffianDescent.VoisinRelativeSurfaceFibreProjection
import AllCharacteristics.HypersurfaceFiberNaturality

/-!
# Naturality of the fixed cubic surface fibre identification

The explicit coefficient-change morphism between cubic hypersurfaces agrees
with the canonical restriction of the corresponding fibres of the relative
fixed-surface family.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

variable {K T U : Type u} [Field K] [CommRing T] [CommRing U]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (b : K →+* T) (s : Spec (.of T) ⟶ E)
  (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
  (g : T →+* U)

include hs in
theorem fixedCubicSurfaceFamilyFibreRestriction_toGroundField :
    (Spec.map (CommRingCat.ofHom g) ≫ s) ≫ k =
      Spec.map (CommRingCat.ofHom (g.comp b)) := by
  rw [Category.assoc, hs, ← Spec.map_comp]
  rfl

/-- The actual fixed-surface fibre isomorphisms commute with further
coefficient change and the Cartesian fibre restriction. -/
theorem fixedCubicSurfaceFamilyFieldFibreIso_naturality :
    let sg := Spec.map (CommRingCat.ofHom g) ≫ s
    let hsg := fixedCubicSurfaceFamilyFibreRestriction_toGroundField
      k b s hs g
    hypersurfaceCoefficientRestriction b g a ha ≫
        (fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs).inv =
      (fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b) sg hsg).inv ≫
        fixedCubicSurfaceFamilyFibreRestriction a ha k s g := by
  let sg := Spec.map (CommRingCat.ofHom g) ≫ s
  let hsg : sg ≫ k = Spec.map (CommRingCat.ofHom (g.comp b)) :=
    fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
  let eT := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
  let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b) sg hsg
  let c := hypersurfaceCoefficientRestriction b g a ha
  let q := fixedCubicSurfaceFamilyFibreRestriction a ha k s g
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · have hT := fixedCubicSurfaceFamilyRingFibreIso_toGroundSurface
        a ha k b s hs
      have hU := fixedCubicSurfaceFamilyRingFibreIso_toGroundSurface
        a ha k (g.comp b) sg hsg
      have hc := projectiveCoefficientMap_comp_eq b g (g.comp b)
        (equationIdeal a ha)
        (equationIdeal (a.map b) (ha.map b))
        (equationIdeal (a.map (g.comp b)) (ha.map (g.comp b)))
        (equationIdeal_map b a ha)
        (equationIdeal_map_comp b g a ha)
        (equationIdeal_map (g.comp b) a ha) rfl
      have hT' : eT.inv ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
            pullback.fst (hypersurfaceToBase a ha) k =
          projectiveCoefficientMap b (equationIdeal a ha)
            (equationIdeal (a.map b) (ha.map b))
            (equationIdeal_map b a ha) := by
        have H := congrArg (fun m => eT.inv ≫ m) hT.symm
        calc
          _ = eT.inv ≫ (eT.hom ≫
            projectiveCoefficientMap b (equationIdeal a ha)
              (equationIdeal (a.map b) (ha.map b))
              (equationIdeal_map b a ha)) := H
          _ = _ := by
            change (eT.inv ≫ eT.hom) ≫
              projectiveCoefficientMap b (equationIdeal a ha)
                (equationIdeal (a.map b) (ha.map b))
                (equationIdeal_map b a ha) = _
            rw [Iso.inv_hom_id]
            change (𝟙 (scheme (equationIdeal (a.map b) (ha.map b)))) ≫
              projectiveCoefficientMap b (equationIdeal a ha)
                (equationIdeal (a.map b) (ha.map b))
                (equationIdeal_map b a ha) = _
            exact Category.id_comp _
      have hU' : eU.inv ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) sg ≫
            pullback.fst (hypersurfaceToBase a ha) k =
          projectiveCoefficientMap (g.comp b) (equationIdeal a ha)
            (equationIdeal (a.map (g.comp b)) (ha.map (g.comp b)))
            (equationIdeal_map (g.comp b) a ha) := by
        have H := congrArg (fun m => eU.inv ≫ m) hU.symm
        calc
          _ = eU.inv ≫ (eU.hom ≫
            projectiveCoefficientMap (g.comp b) (equationIdeal a ha)
              (equationIdeal (a.map (g.comp b)) (ha.map (g.comp b)))
              (equationIdeal_map (g.comp b) a ha)) := H
          _ = _ := by
            change (eU.inv ≫ eU.hom) ≫
              projectiveCoefficientMap (g.comp b) (equationIdeal a ha)
                (equationIdeal (a.map (g.comp b)) (ha.map (g.comp b)))
                (equationIdeal_map (g.comp b) a ha) = _
            rw [Iso.inv_hom_id]
            change (𝟙 (scheme (equationIdeal (a.map (g.comp b))
              (ha.map (g.comp b))))) ≫
              projectiveCoefficientMap (g.comp b) (equationIdeal a ha)
                (equationIdeal (a.map (g.comp b)) (ha.map (g.comp b)))
                (equationIdeal_map (g.comp b) a ha) = _
            exact Category.id_comp _
      simp only [Category.assoc, fixedCubicSurfaceFamilyFibreRestriction_fst]
      change c ≫ (eT.inv ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
            pullback.fst (hypersurfaceToBase a ha) k) =
        eU.inv ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) sg ≫
            pullback.fst (hypersurfaceToBase a ha) k
      rw [hT', hU']
      exact hc
    · have hTbase := fixedCubicSurfaceFamilyRingFibreIso_toBase
        a ha k b s hs
      have hUbase := fixedCubicSurfaceFamilyRingFibreIso_toBase
        a ha k (g.comp b) sg hsg
      have hTbase' : eT.inv ≫
          pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s =
          hypersurfaceToBase (a.map b) (ha.map b) := by
        have H := congrArg (fun m => eT.inv ≫ m) hTbase.symm
        calc
          _ = eT.inv ≫ (eT.hom ≫
            hypersurfaceToBase (a.map b) (ha.map b)) := H
          _ = _ := by
            change (eT.inv ≫ eT.hom) ≫
              hypersurfaceToBase (a.map b) (ha.map b) = _
            simp only [Iso.inv_hom_id, Category.id_comp]
      have hUbase' : eU.inv ≫
          pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) sg =
          hypersurfaceToBase (a.map (g.comp b))
            (ha.map (g.comp b)) := by
        have H := congrArg (fun m => eU.inv ≫ m) hUbase.symm
        calc
          _ = eU.inv ≫ (eU.hom ≫
            hypersurfaceToBase (a.map (g.comp b))
              (ha.map (g.comp b))) := H
          _ = _ := by
            change (eU.inv ≫ eU.hom) ≫
              hypersurfaceToBase (a.map (g.comp b))
                (ha.map (g.comp b)) = _
            simp only [Iso.inv_hom_id, Category.id_comp]
      dsimp only [eT, eU, c, q] at hTbase' hUbase' ⊢
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc
        (fixedCubicSurfaceFamilyFibreRestriction a ha k s g)
        (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s) s]
      rw [fixedCubicSurfaceFamilyFibreRestriction_snd]
      simp only [← Category.assoc, hTbase']
      rw [hUbase']
      exact congrArg (fun m => m ≫ s)
        (hypersurfaceCoefficientRestriction_toBase b g a ha)
  · have hTbase := fixedCubicSurfaceFamilyRingFibreIso_toBase
      a ha k b s hs
    have hUbase := fixedCubicSurfaceFamilyRingFibreIso_toBase
      a ha k (g.comp b) sg hsg
    have hTbase' : eT.inv ≫
        pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s =
        hypersurfaceToBase (a.map b) (ha.map b) := by
      have H := congrArg (fun m => eT.inv ≫ m) hTbase.symm
      calc
        _ = eT.inv ≫ (eT.hom ≫
          hypersurfaceToBase (a.map b) (ha.map b)) := H
        _ = _ := by
          change (eT.inv ≫ eT.hom) ≫
            hypersurfaceToBase (a.map b) (ha.map b) = _
          simp only [Iso.inv_hom_id, Category.id_comp]
    have hUbase' : eU.inv ≫
        pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) sg =
        hypersurfaceToBase (a.map (g.comp b))
          (ha.map (g.comp b)) := by
      have H := congrArg (fun m => eU.inv ≫ m) hUbase.symm
      calc
        _ = eU.inv ≫ (eU.hom ≫
          hypersurfaceToBase (a.map (g.comp b))
            (ha.map (g.comp b))) := H
        _ = _ := by
          change (eU.inv ≫ eU.hom) ≫
            hypersurfaceToBase (a.map (g.comp b))
              (ha.map (g.comp b)) = _
          simp only [Iso.inv_hom_id, Category.id_comp]
    dsimp only [eT, eU, c, q] at hTbase' hUbase' ⊢
    simp only [Category.assoc]
    rw [fixedCubicSurfaceFamilyFibreRestriction_snd]
    simp only [← Category.assoc, hTbase']
    rw [hUbase']
    exact hypersurfaceCoefficientRestriction_toBase b g a ha

end PfaffianDescent
