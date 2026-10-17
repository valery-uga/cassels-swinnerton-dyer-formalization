import PfaffianDescent.VoisinCanonicalAffineUniversalIdealComparison

/-!
# Affine refinement of an arbitrary Voisin parameter change

After pulling the normalized affine parameter cover back along any scheme
morphism, affine refinement gives actual coefficient-ring maps on every
member. These maps recover the original parameter morphism by composition.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {K : Type u} [Field K]
  {E Y : Scheme.{u}}
  (h : E ⟶ projectiveParameters K (Fin 4) 3)
  (f : Y ⟶ E)

/-- Pull back the normalized affine parameter cover. -/
noncomputable def fixedCubicParameterChangeOpenCover : Y.OpenCover :=
  (fixedCubicParameterChartAffineCover h).openCover.pullback₁ f

/-- An affine open cover of the source of an arbitrary parameter change,
subordinate to the normalized affine parameter cover. -/
noncomputable def fixedCubicParameterChangeAffineCover : Y.AffineOpenCover :=
  (fixedCubicParameterChangeOpenCover h f).affineRefinement

/-- The canonical map from a refined source member to the corresponding
normalized affine parameter member. -/
noncomputable def fixedCubicParameterChangeChartMap
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    Spec (.of ((fixedCubicParameterChangeAffineCover h f).X i)) ⟶
      Spec (.of ((fixedCubicParameterChartAffineCover h).X i.1)) :=
  ((fixedCubicParameterChangeOpenCover h f).X i.1).affineCover.f i.2 ≫
    (fixedCubicParameterChartAffineCover h).openCover.pullbackHom f i.1

/-- The coefficient-ring map induced by the actual chart map. -/
noncomputable def fixedCubicParameterChangeCoefficientMap
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    (fixedCubicParameterChartAffineCover h).X i.1 →+*
      (fixedCubicParameterChangeAffineCover h f).X i :=
  (Spec.preimage (fixedCubicParameterChangeChartMap h f i)).hom

/-- Every refined affine source member factors through its normalized
affine parameter-chart member by the specified coefficient map. -/
theorem fixedCubicParameterChangeAffineCover_factor
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    (fixedCubicParameterChangeAffineCover h f).f i ≫ f =
      Spec.map (CommRingCat.ofHom
        (fixedCubicParameterChangeCoefficientMap h f i)) ≫
        (fixedCubicParameterChartAffineCover h).f i.1 := by
  let 𝒜 := fixedCubicParameterChartAffineCover h
  let 𝒰 := fixedCubicParameterChangeOpenCover h f
  change ((𝒰.X i.1).affineCover.f i.2 ≫ 𝒰.f i.1) ≫ f =
    Spec.map (Spec.preimage
      ((𝒰.X i.1).affineCover.f i.2 ≫ 𝒜.openCover.pullbackHom f i.1)) ≫
      𝒜.f i.1
  rw [Spec.map_preimage]
  have H : 𝒰.f i.1 ≫ f = 𝒜.openCover.pullbackHom f i.1 ≫ 𝒜.f i.1 :=
    (Scheme.Cover.pullbackHom_map 𝒜.openCover f i.1).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun w => (𝒰.X i.1).affineCover.f i.2 ≫ w) H).trans
      (Category.assoc _ _ _).symm)

/-- The induced coefficient map is compatible with the ground-field map
of the arbitrary parameter change. -/
theorem fixedCubicParameterChangeCoefficientMap_toBase
    (k : E ⟶ Spec (.of K))
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    let T := (fixedCubicParameterChartAffineCover h).X i.1
    let U := (fixedCubicParameterChangeAffineCover h f).X i
    letI : Algebra K T :=
      fixedCubicParameterChartAffineCover_groundAlgebra k h i.1
    let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
    g.comp (algebraMap K T) =
      (Spec.preimage
        ((fixedCubicParameterChangeAffineCover h f).f i ≫ f ≫ k)).hom := by
  let T := (fixedCubicParameterChartAffineCover h).X i.1
  let U := (fixedCubicParameterChangeAffineCover h f).X i
  letI : Algebra K T :=
    fixedCubicParameterChartAffineCover_groundAlgebra k h i.1
  let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
  have hs : (fixedCubicParameterChartAffineCover h).f i.1 ≫ k =
      Spec.map (CommRingCat.ofHom (algebraMap K T)) :=
    fixedCubicParameterChartAffineCover_toBase k h i.1
  have hf := fixedCubicParameterChangeAffineCover_factor h f i
  have H : CommRingCat.ofHom (g.comp (algebraMap K T)) =
      Spec.preimage ((fixedCubicParameterChangeAffineCover h f).f i ≫ f ≫ k) := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (g.comp (algebraMap K T))) =
      Spec.map (Spec.preimage
        ((fixedCubicParameterChangeAffineCover h f).f i ≫ f ≫ k))
    rw [Spec.map_preimage]
    change Spec.map (CommRingCat.ofHom (algebraMap K T) ≫
      CommRingCat.ofHom g) = _
    rw [Spec.map_comp]
    calc
      Spec.map (CommRingCat.ofHom g) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom g) ≫
          ((fixedCubicParameterChartAffineCover h).f i.1 ≫ k) := by rw [hs]
      _ = ((fixedCubicParameterChangeAffineCover h f).f i ≫ f) ≫ k := by
        rw [← Category.assoc, ← hf]
      _ = _ := by rw [Category.assoc]
  exact congrArg CommRingCat.Hom.hom H

set_option backward.isDefEq.respectTransparency false in
/-- On each affine member of an arbitrary parameter change, the canonical
surface-family restriction satisfies universal ideal base change. -/
theorem fixedCubicParameterChangeAffineCover_canonicalUniversalIdealBaseChange
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (k : E ⟶ Spec (.of K))
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h))
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    let j := i.1
    let T := (fixedCubicParameterChartAffineCover h).X j
    let U := (fixedCubicParameterChangeAffineCover h f).X i
    letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h j
    let b := algebraMap K T
    let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
    let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f j
    let hs : s ≫ k = Spec.map (CommRingCat.ofHom b) :=
      fixedCubicParameterChartAffineCover_toBase k h j
    let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
    let sg := Spec.map (CommRingCat.ofHom g) ≫ s
    let hsg := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
    let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b) sg hsg
    let q := fixedCubicSurfaceFamilyFibreRestriction a ha k s g
    let v := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s
    IsIso (closedImmersionIdealBaseChangeHom
      (((eqToHom (congrArg scheme hJ) ≫ eU.inv) ≫ q) ≫ v)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) := by
  exact fixedCubicParameterChartAffineCover_canonicalUniversalIdealBaseChange
    a ha k h hk hflat i.1 (fixedCubicParameterChangeCoefficientMap h f i)

end PfaffianDescent
