import PfaffianDescent.VoisinRelativeRingFibreConcrete
import PfaffianDescent.VoisinRelativeTwoCubicIntersection
import PfaffianDescent.AmbientCoefficientProductMono

/-!
# The relative two-cubic intersection over an arbitrary coefficient ring

On a normalized coefficient chart, the actual relative universal-equation
zero locus over a ring-valued parameter is the intersection of the fixed
cubic and the specialized normalized moving cubic. The comparison keeps
both maps to the ambient projective space and to the coefficient spectrum.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A normalized chart factorization over the ground field determines its
coefficient-ring map uniquely. -/
theorem normalizedParameterChart_baseMap
    {K T : Type u} [CommRing K] [CommRing T]
    {E : Scheme.{u}}
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (k : E ⟶ Spec (.of K))
    (hk : h ≫ projectiveParametersToBase K (Fin 4) 3 = k)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j) :
    f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b := by
  have hmap : Spec.map (CommRingCat.ofHom
      (f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j))) =
      Spec.map (CommRingCat.ofHom b) := by
    calc
    Spec.map (CommRingCat.ofHom
        (f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j))) =
      (Spec.map (CommRingCat.ofHom f) ≫
        parameterChartι K (Fin 4) 3 j) ≫
          projectiveParametersToBase K (Fin 4) 3 := by
            rw [Category.assoc, parameterChartι_toBase, ← Spec.map_comp]
            rfl
    _ = (s ≫ h) ≫ projectiveParametersToBase K (Fin 4) 3 := by rw [heq]
    _ = s ≫ k := by rw [Category.assoc, hk]
      _ = Spec.map (CommRingCat.ofHom b) := hs
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hmap)

/-- The actual relative zero-locus fibre over a normalized coefficient
chart is the scheme-theoretic intersection of two concrete cubic
hypersurfaces over an arbitrary commutative coefficient ring. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    pullback (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≅
      pullback
        (prod.lift
          (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
          (hypersurfaceToBase (a.map b) (ha.map b)))
        (prod.lift
          (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
          (hypersurfaceToBase q hq)) := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
  let eY := normalizedUniversalEquationRingFibreOfParameterIso h s j f heq
  let f₀ := prod.lift
    (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
    (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s)
  let g₀ := prod.lift
    (pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
      projectiveUniversalToAmbient K (Fin 4) 3)
    (pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h))
  let F := prod.lift
    (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
    (hypersurfaceToBase (a.map b) (ha.map b))
  let G := prod.lift
    (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
    (hypersurfaceToBase q hq)
  have hF : f₀ = eX.hom ≫ F := by
    apply prod.hom_ext
    · simp only [Category.assoc, f₀, F, prod.lift_fst]
      exact (fixedCubicSurfaceFamilyRingFibreIso_toAmbient a ha k b s hs).symm
    · simp only [Category.assoc, f₀, F, prod.lift_snd]
      exact (fixedCubicSurfaceFamilyRingFibreIso_toBase a ha k b s hs).symm
  have hG : g₀ = eY.hom ≫ G := by
    apply prod.hom_ext
    · simp only [Category.assoc, g₀, G, prod.lift_fst]
      rw [← hb]
      exact (normalizedUniversalEquationRingFibreOfParameterIso_hom_toAmbient
        h s j f heq).symm
    · simp only [Category.assoc, g₀, G, prod.lift_snd]
      exact (normalizedUniversalEquationRingFibreOfParameterIso_hom_toBase
        h s j f heq).symm
  exact fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso a ha k h s ≪≫
    pullbackTransportIso eX eY F G f₀ g₀ hF hG

/-- The two-cubic ring-fibre comparison is over the coefficient spectrum. -/
theorem fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso_toBase
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    (fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso
      a ha k h b s hs j f heq hb).hom ≫
      pullback.fst
        (prod.lift
          (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
          (hypersurfaceToBase (a.map b) (ha.map b)))
        (prod.lift
          (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
          (hypersurfaceToBase q hq)) ≫
            hypersurfaceToBase (a.map b) (ha.map b) =
      pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
  let eY := normalizedUniversalEquationRingFibreOfParameterIso h s j f heq
  let f₀ := prod.lift
    (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
    (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s)
  let g₀ := prod.lift
    (pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
      projectiveUniversalToAmbient K (Fin 4) 3)
    (pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h))
  let F := prod.lift
    (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
    (hypersurfaceToBase (a.map b) (ha.map b))
  let G := prod.lift
    (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
    (hypersurfaceToBase q hq)
  have hF : f₀ = eX.hom ≫ F := by
    apply prod.hom_ext
    · simp only [Category.assoc, f₀, F, prod.lift_fst]
      exact (fixedCubicSurfaceFamilyRingFibreIso_toAmbient a ha k b s hs).symm
    · simp only [Category.assoc, f₀, F, prod.lift_snd]
      exact (fixedCubicSurfaceFamilyRingFibreIso_toBase a ha k b s hs).symm
  have hG : g₀ = eY.hom ≫ G := by
    apply prod.hom_ext
    · simp only [Category.assoc, g₀, G, prod.lift_fst]
      rw [← hb]
      exact (normalizedUniversalEquationRingFibreOfParameterIso_hom_toAmbient
        h s j f heq).symm
    · simp only [Category.assoc, g₀, G, prod.lift_snd]
      exact (normalizedUniversalEquationRingFibreOfParameterIso_hom_toBase
        h s j f heq).symm
  let e₀ := fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso a ha k h s
  let e₁ := pullbackTransportIso eX eY F G f₀ g₀ hF hG
  have h₁ : e₁.hom ≫ pullback.fst F G =
      pullback.fst f₀ g₀ ≫ eX.hom :=
    pullbackTransportIso_hom_fst eX eY F G f₀ g₀ hF hG
  have hX : eX.hom ≫ hypersurfaceToBase (a.map b) (ha.map b) =
      pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s :=
    fixedCubicSurfaceFamilyRingFibreIso_toBase a ha k b s hs
  change ((e₀ ≪≫ e₁).hom ≫ pullback.fst F G) ≫
    hypersurfaceToBase (a.map b) (ha.map b) = _
  calc
    _ = e₀.hom ≫ pullback.fst f₀ g₀ ≫ eX.hom ≫
        hypersurfaceToBase (a.map b) (ha.map b) := by
          simpa only [Iso.trans_hom, Category.assoc] using
            congrArg (fun t => e₀.hom ≫ t ≫
              hypersurfaceToBase (a.map b) (ha.map b)) h₁
    _ = e₀.hom ≫ pullback.fst f₀ g₀ ≫
        pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s := by
          simpa only [Category.assoc] using
            congrArg (fun t => e₀.hom ≫ pullback.fst f₀ g₀ ≫ t) hX
    _ = _ := fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso_toBase
      a ha k h s

/-- The two-cubic ring-fibre comparison also preserves the point of the
fixed cubic surface family, after undoing the fixed-cubic base change. -/
theorem fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso_toSurface
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    (fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso
      a ha k h b s hs j f heq hb).hom ≫
      pullback.fst
        (prod.lift
          (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
          (hypersurfaceToBase (a.map b) (ha.map b)))
        (prod.lift
          (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
          (hypersurfaceToBase q hq)) ≫
      (fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs).inv ≫
      pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s =
    pullback.fst (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≫
      fixedCubicSurfaceEquationZeroLocusToSurface a ha k h := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
  let eY := normalizedUniversalEquationRingFibreOfParameterIso h s j f heq
  let f₀ := prod.lift
    (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
    (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s)
  let g₀ := prod.lift
    (pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
      projectiveUniversalToAmbient K (Fin 4) 3)
    (pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h))
  let F := prod.lift
    (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
    (hypersurfaceToBase (a.map b) (ha.map b))
  let G := prod.lift
    (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
    (hypersurfaceToBase q hq)
  have hF : f₀ = eX.hom ≫ F := by
    apply prod.hom_ext
    · simp only [Category.assoc, f₀, F, prod.lift_fst]
      exact (fixedCubicSurfaceFamilyRingFibreIso_toAmbient a ha k b s hs).symm
    · simp only [Category.assoc, f₀, F, prod.lift_snd]
      exact (fixedCubicSurfaceFamilyRingFibreIso_toBase a ha k b s hs).symm
  have hG : g₀ = eY.hom ≫ G := by
    apply prod.hom_ext
    · simp only [Category.assoc, g₀, G, prod.lift_fst]
      rw [← hb]
      exact (normalizedUniversalEquationRingFibreOfParameterIso_hom_toAmbient
        h s j f heq).symm
    · simp only [Category.assoc, g₀, G, prod.lift_snd]
      exact (normalizedUniversalEquationRingFibreOfParameterIso_hom_toBase
        h s j f heq).symm
  let e₀ := fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso a ha k h s
  let e₁ := pullbackTransportIso eX eY F G f₀ g₀ hF hG
  have h₁ : e₁.hom ≫ pullback.fst F G =
      pullback.fst f₀ g₀ ≫ eX.hom :=
    pullbackTransportIso_hom_fst eX eY F G f₀ g₀ hF hG
  change ((e₀ ≪≫ e₁).hom ≫ pullback.fst F G) ≫ eX.inv ≫
    pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s = _
  calc
    _ = e₀.hom ≫ pullback.fst f₀ g₀ ≫ eX.hom ≫ eX.inv ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s := by
            simpa only [Iso.trans_hom, Category.assoc] using
              congrArg (fun t => e₀.hom ≫ t ≫ eX.inv ≫
                pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s) h₁
    _ = e₀.hom ≫ pullback.fst f₀ g₀ ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s := by
            simp only [Iso.hom_inv_id_assoc]
    _ = _ := by
      simpa only [e₀, f₀, g₀] using
        (fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso_toSurface a ha k h s)

/-- Over an arbitrary coefficient ring, the relative zero-locus fibre is
the actual projective scheme of the sum of the fixed and normalized cubic
equation ideals. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    pullback (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≅
      scheme (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal q hq) := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  exact fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso
      a ha k h b s hs j f heq hb ≪≫
    (twoHypersurfaceCoefficientProductIso b (Fin 4)
      (a.map b) q (ha.map b) hq).symm

/-- The projective-scheme presentation of the actual relative fibre is
an isomorphism over the coefficient spectrum. -/
theorem fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso_toBase
    {K T : Type u} [Field K] [CommRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (b : K →+* T) (s : Spec (.of T) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j)
    (hb : f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j) = b) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    (fixedCubicSurfaceEquationZeroLocusProjectiveRingFibreIso
      a ha k h b s hs j f heq hb).hom ≫
      toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal q hq) =
      pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  let e₀ := fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso
    a ha k h b s hs j f heq hb
  let e₁ := twoHypersurfaceCoefficientProductIso b (Fin 4)
    (a.map b) q (ha.map b) hq
  let F := prod.lift
    (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
    (hypersurfaceToBase (a.map b) (ha.map b))
  let G := prod.lift
    (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
    (hypersurfaceToBase q hq)
  have h₁ : e₁.inv ≫
      toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal q hq) =
      pullback.fst F G ≫ hypersurfaceToBase (a.map b) (ha.map b) := by
    exact projectiveIntersectionCoefficientProductIso_inv_toBase b (Fin 4)
      (equationIdeal (a.map b) (ha.map b)) (equationIdeal q hq)
  change (e₀ ≪≫ e₁.symm).hom ≫
    toBase (equationIdeal (a.map b) (ha.map b) ⊔ equationIdeal q hq) = _
  calc
    _ = e₀.hom ≫ pullback.fst F G ≫
        hypersurfaceToBase (a.map b) (ha.map b) := by
          simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using
            congrArg (fun t => e₀.hom ≫ t) h₁
    _ = _ := fixedCubicSurfaceEquationZeroLocusTwoCubicRingFibreIso_toBase
      a ha k h b s hs j f heq hb


end PfaffianDescent
