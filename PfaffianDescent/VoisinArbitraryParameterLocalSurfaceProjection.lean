import PfaffianDescent.VoisinArbitraryParameterAffineRefinement
import PfaffianDescent.ClosedImmersionIdealBaseChangeSourceIso

/-!
# Canonical projection of the actual affine source fibres

Each coefficient-changed cubic model maps to the fibre of the constant
surface family over the actual affine source member. Its map into the global
surface family is the ordinary pullback projection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

/-- Transporting a pullback along equality of its right parameter leaves
the projection to the left scheme unchanged. -/
theorem eqToHom_pullback_fst
    {X Y Z : Scheme.{u}} (p : X ⟶ Z) {s t : Y ⟶ Z}
    (hs : s = t) :
    eqToHom (congrArg (fun m : Y ⟶ Z => pullback p m) hs) ≫ pullback.fst p t =
      pullback.fst p s := by
  cases hs
  simp

variable {K : Type u} [Field K]
  {E Y : Scheme.{u}}
  (h : E ⟶ projectiveParameters K (Fin 4) 3)
  (f : Y ⟶ E)

/-- The map from each refined affine source member to the parameter scheme
is the coefficient-map composite used in the local cubic model. -/
theorem fixedCubicParameterChangeAffineCover_toParameter
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    let T := (fixedCubicParameterChartAffineCover h).X i.1
    let U := (fixedCubicParameterChangeAffineCover h f).X i
    let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
    let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f i.1
    (fixedCubicParameterChangeAffineCover h f).f i ≫ f =
      Spec.map (CommRingCat.ofHom g) ≫ s :=
  fixedCubicParameterChangeAffineCover_factor h f i

set_option backward.isDefEq.respectTransparency false in
/-- The explicit local map into the global constant surface family equals
the projection from the fibre over the actual affine source member. -/
theorem fixedCubicParameterChangeAffineCover_surfaceProjection
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (k : E ⟶ Spec (.of K))
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    let T := (fixedCubicParameterChartAffineCover h).X i.1
    let U := (fixedCubicParameterChangeAffineCover h f).X i
    letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h i.1
    let b := algebraMap K T
    let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
    let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f i.1
    let si := (fixedCubicParameterChangeAffineCover h f).f i ≫ f
    let hs : s ≫ k = Spec.map (CommRingCat.ofHom b) :=
      fixedCubicParameterChartAffineCover_toBase k h i.1
    let hsi := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
    let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b)
      (Spec.map (CommRingCat.ofHom g) ≫ s) hsi
    let q := fixedCubicSurfaceFamilyFibreRestriction a ha k s g
    let v := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s
    let hf := fixedCubicParameterChangeAffineCover_factor h f i
    (eU.inv ≫ q) ≫ v =
      (eU.inv ≫ eqToHom (congrArg
        (fun m : Spec (.of U) ⟶ E =>
          pullback (pullback.snd (hypersurfaceToBase a ha) k) m) hf.symm)) ≫
        pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) si := by
  let T := (fixedCubicParameterChartAffineCover h).X i.1
  let U := (fixedCubicParameterChangeAffineCover h f).X i
  letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h i.1
  let b := algebraMap K T
  let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
  let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f i.1
  let si := (fixedCubicParameterChangeAffineCover h f).f i ≫ f
  let hs : s ≫ k = Spec.map (CommRingCat.ofHom b) :=
    fixedCubicParameterChartAffineCover_toBase k h i.1
  let hsi := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
  let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b)
    (Spec.map (CommRingCat.ofHom g) ≫ s) hsi
  let q := fixedCubicSurfaceFamilyFibreRestriction a ha k s g
  let v := pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s
  let hf := fixedCubicParameterChangeAffineCover_factor h f i
  change (eU.inv ≫ q) ≫ v =
    (eU.inv ≫ eqToHom (congrArg
      (fun m : Spec (.of U) ⟶ E =>
        pullback (pullback.snd (hypersurfaceToBase a ha) k) m) hf.symm)) ≫
      pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) si
  rw [Category.assoc, fixedCubicSurfaceFamilyFibreRestriction_fst]
  rw [Category.assoc, eqToHom_pullback_fst _ hf.symm]

set_option backward.isDefEq.respectTransparency false in
/-- The ideal comparison on an arbitrary refined source member uses the
actual projection from the local pullback of the global surface family. -/
theorem fixedCubicParameterChangeAffineCover_projectionIdealBaseChange
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (k : E ⟶ Spec (.of K))
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h))
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    let T := (fixedCubicParameterChartAffineCover h).X i.1
    let U := (fixedCubicParameterChangeAffineCover h f).X i
    letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h i.1
    let b := algebraMap K T
    let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
    let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f i.1
    let si := (fixedCubicParameterChangeAffineCover h f).f i ≫ f
    let hs : s ≫ k = Spec.map (CommRingCat.ofHom b) :=
      fixedCubicParameterChartAffineCover_toBase k h i.1
    let hsi := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
    let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b)
      (Spec.map (CommRingCat.ofHom g) ≫ s) hsi
    let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
    let hf := fixedCubicParameterChangeAffineCover_factor h f i
    let p := pullback.snd (hypersurfaceToBase a ha) k
    IsIso (closedImmersionIdealBaseChangeHom
      ((eqToHom (congrArg scheme hJ) ≫ eU.inv ≫
          eqToHom (congrArg (fun m : Spec (.of U) ⟶ E => pullback p m)
            hf.symm)) ≫ pullback.fst p si)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) := by
  let T := (fixedCubicParameterChartAffineCover h).X i.1
  let U := (fixedCubicParameterChangeAffineCover h f).X i
  letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h i.1
  let b := algebraMap K T
  let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
  let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f i.1
  let si := (fixedCubicParameterChangeAffineCover h f).f i ≫ f
  let hs : s ≫ k = Spec.map (CommRingCat.ofHom b) :=
    fixedCubicParameterChartAffineCover_toBase k h i.1
  let hsi := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
  let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b)
    (Spec.map (CommRingCat.ofHom g) ≫ s) hsi
  let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
  let hf := fixedCubicParameterChangeAffineCover_factor h f i
  let p := pullback.snd (hypersurfaceToBase a ha) k
  let q := fixedCubicSurfaceFamilyFibreRestriction a ha k s g
  let v := pullback.fst p s
  have hlocal := fixedCubicParameterChangeAffineCover_canonicalUniversalIdealBaseChange
    h f a ha k hk hflat i
  have hproj := fixedCubicParameterChangeAffineCover_surfaceProjection
    h f a ha k i
  change IsIso (closedImmersionIdealBaseChangeHom
    (((eqToHom (congrArg scheme hJ) ≫ eU.inv) ≫ q) ≫ v)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) at hlocal
  change (eU.inv ≫ q) ≫ v =
    (eU.inv ≫ eqToHom (congrArg (fun m : Spec (.of U) ⟶ E => pullback p m)
      hf.symm)) ≫ pullback.fst p si at hproj
  have hmap : (((eqToHom (congrArg scheme hJ) ≫ eU.inv) ≫ q) ≫ v) =
      ((eqToHom (congrArg scheme hJ) ≫ eU.inv ≫
          eqToHom (congrArg (fun m : Spec (.of U) ⟶ E => pullback p m)
            hf.symm)) ≫ pullback.fst p si) := by
    calc
      _ = eqToHom (congrArg scheme hJ) ≫ ((eU.inv ≫ q) ≫ v) := by
        simp only [Category.assoc]
      _ = eqToHom (congrArg scheme hJ) ≫
          ((eU.inv ≫ eqToHom (congrArg
            (fun m : Spec (.of U) ⟶ E => pullback p m) hf.symm)) ≫
            pullback.fst p si) := congrArg _ hproj
      _ = _ := by simp only [Category.assoc]
  rw [hmap] at hlocal
  exact hlocal

set_option backward.isDefEq.respectTransparency false in
/-- The canonical ideal comparison holds on the actual constant-surface
fibre over every refined affine member of an arbitrary parameter change. -/
theorem fixedCubicParameterChangeAffineCover_actualFibreIdealBaseChange
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (k : E ⟶ Spec (.of K))
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (hflat : Flat (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h))
    (i : (fixedCubicParameterChangeAffineCover h f).I₀) :
    let p := pullback.snd (hypersurfaceToBase a ha) k
    let si := (fixedCubicParameterChangeAffineCover h f).f i ≫ f
    IsIso (closedImmersionIdealBaseChangeHom
      (pullback.fst p si)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) := by
  let T := (fixedCubicParameterChartAffineCover h).X i.1
  let U := (fixedCubicParameterChangeAffineCover h f).X i
  letI : Algebra K T := fixedCubicParameterChartAffineCover_groundAlgebra k h i.1
  let b := algebraMap K T
  let g : T →+* U := fixedCubicParameterChangeCoefficientMap h f i
  let s : Spec (.of T) ⟶ E := (fixedCubicParameterChartAffineCover h).f i.1
  let si := (fixedCubicParameterChangeAffineCover h f).f i ≫ f
  let hs : s ≫ k = Spec.map (CommRingCat.ofHom b) :=
    fixedCubicParameterChartAffineCover_toBase k h i.1
  let hsi := fixedCubicSurfaceFamilyFibreRestriction_toGroundField k b s hs g
  let eU := fixedCubicSurfaceFamilyFieldFibreIso a ha k (g.comp b)
    (Spec.map (CommRingCat.ofHom g) ≫ s) hsi
  let hJ := coefficientChangedHomogeneousIdeal_equationIdeal_map_comp a ha b g
  let hf := fixedCubicParameterChangeAffineCover_factor h f i
  let p := pullback.snd (hypersurfaceToBase a ha) k
  let e : scheme (coefficientChangedHomogeneousIdeal g
        (equationIdeal (a.map b) (ha.map b))) ≅ pullback p si :=
    eqToIso (congrArg scheme hJ) ≪≫ eU.symm ≪≫
      eqToIso (congrArg (fun m : Spec (.of U) ⟶ E => pullback p m) hf.symm)
  have hmodel := fixedCubicParameterChangeAffineCover_projectionIdealBaseChange
    h f a ha k hk hflat i
  change IsIso (closedImmersionIdealBaseChangeHom
    (e.hom ≫ pullback.fst p si)
    (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) at hmodel
  letI : IsIso (closedImmersionIdealBaseChangeHom
      (e.hom ≫ pullback.fst p si)
      (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) := hmodel
  exact isIso_closedImmersionIdealBaseChangeHom_of_sourceIso e
    (pullback.fst p si)
    (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)

end PfaffianDescent
