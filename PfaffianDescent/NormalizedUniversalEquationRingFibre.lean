import AllCharacteristics.UniversalProjectiveFamilyCharts
import AllCharacteristics.UniversalProjectiveAmbient
import AllCharacteristics.HypersurfaceCoefficientNaturality
import PfaffianDescent.PullbackSourceIso

/-!
# Normalized universal-equation fibres over arbitrary rings

The universal projective hypersurface restricted to a normalized coefficient
chart is the normalized hypersurface. This remains true after arbitrary
coefficient change, without assuming the target ring is a field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual universal projective equation fibre over an arbitrary point
of a normalized coefficient chart is the hypersurface of the specialized
normalized equation. -/
noncomputable def normalizedUniversalEquationRingFibreIso
    {K T : Type u} [Field K] [CommRing T]
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T) :
    pullback (projectiveUniversalToBase K (Fin 4) 3)
      (Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j) ≅
      hypersurface ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f) := by
  let U := projectiveUniversalToBase K (Fin 4) 3
  let c := parameterChartι K (Fin 4) 3 j
  let t := Spec.map (CommRingCat.ofHom f)
  let e := projectiveUniversalChartFiberIso K (Fin 4) 3 j
  let P := normalizedForm K (Fin 4) 3 j
  let hP := normalizedForm_isHomogeneous K (Fin 4) 3 j
  have he : pullback.snd U c = e.inv ≫ hypersurfaceToBase P hP := by
    change pullback.snd U c = e.inv ≫ normalizedFamilyToBase K (Fin 4) 3 j
    rw [← projectiveUniversalChartFiberIso_hom_snd]
    change pullback.snd U c = (e.inv ≫ e.hom) ≫ pullback.snd U c
    simp
  exact (pullbackLeftPullbackSndIso U c t).symm ≪≫
    pullbackTransportIso e.symm (Iso.refl (Spec (.of T)))
      (hypersurfaceToBase P hP) t
      (pullback.snd U c) t he (by simp) ≪≫
    (hypersurfaceBaseChangeIso f P hP).symm

/-- The same ring-level fibre identification after a parameter morphism
factors through the normalized coefficient chart. This is the form needed
for the relative zero locus over a local point of its parameter scheme. -/
noncomputable def normalizedUniversalEquationRingFibreOfParameterIso
    {K T : Type u} [Field K] [CommRing T]
    {E : Scheme.{u}}
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (s : Spec (.of T) ⟶ E)
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j) :
    pullback (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≅
      hypersurface ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f) :=
  pullback.congrHom rfl heq ≪≫ normalizedUniversalEquationRingFibreIso j f

/-- The arbitrary-ring normalized fibre comparison preserves the point of
the coefficient base. -/
theorem normalizedUniversalEquationRingFibreIso_hom_toBase
    {K T : Type u} [Field K] [CommRing T]
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T) :
    (normalizedUniversalEquationRingFibreIso j f).hom ≫
      hypersurfaceToBase ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f) =
      pullback.snd (projectiveUniversalToBase K (Fin 4) 3)
        (Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j) := by
  let U := projectiveUniversalToBase K (Fin 4) 3
  let c := parameterChartι K (Fin 4) 3 j
  let t := Spec.map (CommRingCat.ofHom f)
  let e := projectiveUniversalChartFiberIso K (Fin 4) 3 j
  let P := normalizedForm K (Fin 4) 3 j
  let hP := normalizedForm_isHomogeneous K (Fin 4) 3 j
  have he : pullback.snd U c = e.inv ≫ hypersurfaceToBase P hP := by
    change pullback.snd U c = e.inv ≫ normalizedFamilyToBase K (Fin 4) 3 j
    rw [← projectiveUniversalChartFiberIso_hom_snd]
    change pullback.snd U c = (e.inv ≫ e.hom) ≫ pullback.snd U c
    simp
  let A := (pullbackLeftPullbackSndIso U c t).symm
  let B := pullbackTransportIso e.symm (Iso.refl (Spec (.of T)))
    (hypersurfaceToBase P hP) t
    (pullback.snd U c) t he (by simp)
  let C := (hypersurfaceBaseChangeIso f P hP).symm
  have hA : A.hom ≫ pullback.snd (pullback.snd U c) t =
      pullback.snd U (t ≫ c) :=
    pullbackLeftPullbackSndIso_inv_snd_snd U c t
  have hB : B.hom ≫ pullback.snd (hypersurfaceToBase P hP) t =
      pullback.snd (pullback.snd U c) t := by
    simpa only [B, Iso.refl_hom, Category.comp_id] using
      (pullbackTransportIso_hom_snd e.symm (Iso.refl (Spec (.of T)))
        (hypersurfaceToBase P hP) t
        (pullback.snd U c) t he (by simp))
  have hC : C.hom ≫ hypersurfaceToBase (P.map f) (hP.map f) =
      pullback.snd (hypersurfaceToBase P hP) t := by
    change (hypersurfaceBaseChangeIso f P hP).inv ≫
      hypersurfaceToBase (P.map f) (hP.map f) =
        pullback.snd (hypersurfaceToBase P hP) (Spec.map (CommRingCat.ofHom f))
    rw [← hypersurfaceBaseChangeIso_hom_snd f P hP]
    simp only [Iso.inv_hom_id_assoc]
  change (A ≪≫ B ≪≫ C).hom ≫ _ = _
  simp only [Iso.trans_hom, Category.assoc]
  rw [hC, hB, hA]

/-- The parameter-factorized arbitrary-ring comparison also preserves the
original coefficient-ring point. -/
theorem normalizedUniversalEquationRingFibreOfParameterIso_hom_toBase
    {K T : Type u} [Field K] [CommRing T]
    {E : Scheme.{u}}
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (s : Spec (.of T) ⟶ E)
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j) :
    (normalizedUniversalEquationRingFibreOfParameterIso h s j f heq).hom ≫
      hypersurfaceToBase ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f) =
      pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) := by
  unfold normalizedUniversalEquationRingFibreOfParameterIso
  rw [Iso.trans_hom, Category.assoc,
    normalizedUniversalEquationRingFibreIso_hom_toBase]
  simp [pullback.congrHom, pullback.map, pullback.lift_snd]

/-- The inverse hypersurface base-change isomorphism preserves the ambient
projective point after the corresponding coefficient map. -/
theorem hypersurfaceBaseChangeIso_inv_toAmbient
    {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T)
    (P : MvPolynomial (Fin 4) R) {d : ℕ} (hP : P.IsHomogeneous d) :
    (hypersurfaceBaseChangeIso f P hP).inv ≫
      (hypersurfaceToAmbient (P.map f) (hP.map f) ≫
        ambientCoefficientMap f) =
      pullback.fst (hypersurfaceToBase P hP)
        (Spec.map (CommRingCat.ofHom f)) ≫
          hypersurfaceToAmbient P hP := by
  have h : (hypersurfaceBaseChangeIso f P hP).hom ≫
      (pullback.fst (hypersurfaceToBase P hP)
        (Spec.map (CommRingCat.ofHom f)) ≫
          hypersurfaceToAmbient P hP) =
      hypersurfaceToAmbient (P.map f) (hP.map f) ≫
        ambientCoefficientMap f := by
    rw [← Category.assoc, hypersurfaceBaseChangeIso_hom_fst]
    exact projectiveCoefficientMap_comp_quotientProjMap f
      (equationIdeal P hP) (equationIdeal (P.map f) (hP.map f))
      (equationIdeal_map f P hP)
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

/-- The normalized chart-fibre comparison preserves the ambient projective
point over the original ground field. -/
theorem normalizedUniversalEquationRingFibreIso_hom_toAmbient
    {K T : Type u} [Field K] [CommRing T]
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T) :
    (normalizedUniversalEquationRingFibreIso j f).hom ≫
      (hypersurfaceToAmbient ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f) ≫
          ambientCoefficientMap
            (f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j))) =
      pullback.fst (projectiveUniversalToBase K (Fin 4) 3)
        (Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j) ≫
          projectiveUniversalToAmbient K (Fin 4) 3 := by
  let U := projectiveUniversalToBase K (Fin 4) 3
  let c := parameterChartι K (Fin 4) 3 j
  let t := Spec.map (CommRingCat.ofHom f)
  let e := projectiveUniversalChartFiberIso K (Fin 4) 3 j
  let P := normalizedForm K (Fin 4) 3 j
  let hP := normalizedForm_isHomogeneous K (Fin 4) 3 j
  let b := chartBaseMap (ParameterIdeal K (Fin 4) 3) j
  have he : pullback.snd U c = e.inv ≫ hypersurfaceToBase P hP := by
    change pullback.snd U c = e.inv ≫ normalizedFamilyToBase K (Fin 4) 3 j
    rw [← projectiveUniversalChartFiberIso_hom_snd]
    change pullback.snd U c = (e.inv ≫ e.hom) ≫ pullback.snd U c
    simp
  let A := (pullbackLeftPullbackSndIso U c t).symm
  let B := pullbackTransportIso e.symm (Iso.refl (Spec (.of T)))
    (hypersurfaceToBase P hP) t (pullback.snd U c) t he (by simp)
  let C := (hypersurfaceBaseChangeIso f P hP).symm
  have hA : A.hom ≫ pullback.fst (pullback.snd U c) t ≫
      pullback.fst U c = pullback.fst U (t ≫ c) :=
    pullbackLeftPullbackSndIso_inv_fst U c t
  have hB : B.hom ≫ pullback.fst (hypersurfaceToBase P hP) t =
      pullback.fst (pullback.snd U c) t ≫ e.inv := by
    simpa only [B, Iso.symm_hom] using
      (pullbackTransportIso_hom_fst e.symm (Iso.refl (Spec (.of T)))
        (hypersurfaceToBase P hP) t
        (pullback.snd U c) t he (by simp))
  have hC : C.hom ≫
      (hypersurfaceToAmbient (P.map f) (hP.map f) ≫
        ambientCoefficientMap (f.comp b)) =
      pullback.fst (hypersurfaceToBase P hP) t ≫
        normalizedFamilyToAmbient K (Fin 4) 3 j := by
    calc
      _ = (C.hom ≫
          (hypersurfaceToAmbient (P.map f) (hP.map f) ≫
            ambientCoefficientMap f)) ≫ ambientCoefficientMap b := by
        rw [← ambientCoefficientMap_comp b f]
        simp only [Category.assoc]
      _ = (pullback.fst (hypersurfaceToBase P hP) t ≫
          hypersurfaceToAmbient P hP) ≫ ambientCoefficientMap b := by
        exact congrArg (· ≫ ambientCoefficientMap b)
          (hypersurfaceBaseChangeIso_inv_toAmbient f P hP)
      _ = _ := by rfl
  have hE : e.inv ≫ normalizedFamilyToAmbient K (Fin 4) 3 j =
      pullback.fst U c ≫ projectiveUniversalToAmbient K (Fin 4) 3 := by
    rw [← projectiveUniversalChartι_toAmbient,
      ← projectiveUniversalChartFiberIso_hom_fst]
    change e.inv ≫ (e.hom ≫ pullback.fst U c ≫
      projectiveUniversalToAmbient K (Fin 4) 3) = _
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hBE : B.hom ≫
      (pullback.fst (hypersurfaceToBase P hP) t ≫
        normalizedFamilyToAmbient K (Fin 4) 3 j) =
      (pullback.fst (pullback.snd U c) t ≫ pullback.fst U c) ≫
        projectiveUniversalToAmbient K (Fin 4) 3 := by
    calc
      _ = (B.hom ≫ pullback.fst (hypersurfaceToBase P hP) t) ≫
          normalizedFamilyToAmbient K (Fin 4) 3 j :=
        (Category.assoc _ _ _).symm
      _ = (pullback.fst (pullback.snd U c) t ≫ e.inv) ≫
          normalizedFamilyToAmbient K (Fin 4) 3 j := by rw [hB]
      _ = pullback.fst (pullback.snd U c) t ≫
          (e.inv ≫ normalizedFamilyToAmbient K (Fin 4) 3 j) :=
        Category.assoc _ _ _
      _ = pullback.fst (pullback.snd U c) t ≫
          (pullback.fst U c ≫ projectiveUniversalToAmbient K (Fin 4) 3) := by
        rw [hE]
      _ = _ := (Category.assoc _ _ _).symm
  change (A ≪≫ B ≪≫ C).hom ≫ _ = _
  simp only [Iso.trans_hom, Category.assoc]
  rw [hC, hBE]
  exact congrArg (· ≫ projectiveUniversalToAmbient K (Fin 4) 3) hA

/-- The parameter-factorized ring-level fibre comparison preserves the
ambient projective point. -/
theorem normalizedUniversalEquationRingFibreOfParameterIso_hom_toAmbient
    {K T : Type u} [Field K] [CommRing T]
    {E : Scheme.{u}}
    (h : E ⟶ projectiveParameters K (Fin 4) 3)
    (s : Spec (.of T) ⟶ E)
    (j : Monomials (Fin 4) 3)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (heq : s ≫ h =
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j) :
    (normalizedUniversalEquationRingFibreOfParameterIso h s j f heq).hom ≫
      (hypersurfaceToAmbient ((normalizedForm K (Fin 4) 3 j).map f)
        ((normalizedForm_isHomogeneous K (Fin 4) 3 j).map f) ≫
          ambientCoefficientMap
            (f.comp (chartBaseMap (ParameterIdeal K (Fin 4) 3) j))) =
      pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
        projectiveUniversalToAmbient K (Fin 4) 3 := by
  unfold normalizedUniversalEquationRingFibreOfParameterIso
  rw [Iso.trans_hom, Category.assoc,
    normalizedUniversalEquationRingFibreIso_hom_toAmbient]
  simp only [pullback.congrHom, asIso_hom, pullback.map]
  rw [← Category.assoc, pullback.lift_fst]
  simp

end PfaffianDescent
