import PfaffianDescent.VoisinRelativeFieldFibreConcrete

/-!
# The concrete two-cubic fibre of the relative zero locus

At a field-valued parameter represented by a nonzero cubic equation `q`,
the relative zero locus is the intersection of the two actual cubic
hypersurfaces over that field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K S : Type u} [Field K] [Field S]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (h : E ⟶ projectiveParameters K (Fin 4) 3)
  (b : K →+* S) (s : Spec (.of S) ⟶ E)
  (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))
  (q : MvPolynomial (Fin 4) S) (hq : q.IsHomogeneous 3)
  (j : Monomials (Fin 4) 3) (hj : q.coeff j.1 ≠ 0)
  (heq : s ≫ h = projectiveEquationParameter b q j hj)

/-- Identify the abstract universal-equation fibre at `s ≫ h` with the
specified concrete cubic hypersurface. -/
noncomputable def relativeEquationFieldFibreIso :
    pullback (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≅
      hypersurface q hq :=
  pullback.congrHom rfl heq ≪≫
    (projectiveEquationFiberIso b q j hj hq).symm

/-- The equation-fibre comparison preserves the ambient projective point. -/
theorem relativeEquationFieldFibreIso_toAmbient :
    (relativeEquationFieldFibreIso h b s q hq j hj heq).hom ≫
      (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b) =
    pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
      projectiveUniversalToAmbient K (Fin 4) 3 := by
  unfold relativeEquationFieldFibreIso
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    projectiveEquationFiberIso_inv_toAmbient b q hq j hj]
  simp only [pullback.congrHom, asIso_hom, pullback.map,
    pullback.lift_fst_assoc, Category.comp_id]

/-- The equation-fibre comparison preserves the field point. -/
theorem relativeEquationFieldFibreIso_toField :
    (relativeEquationFieldFibreIso h b s q hq j hj heq).hom ≫
      hypersurfaceToBase q hq =
    pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) := by
  unfold relativeEquationFieldFibreIso
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    projectiveEquationFiberIso_inv_toField b q hq j hj]
  simp only [pullback.congrHom, asIso_hom, pullback.map,
    pullback.lift_snd, Category.comp_id]

/-- At a specified cubic equation parameter, the actual relative zero-locus
field fibre is the scheme-theoretic intersection of the two concrete cubic
hypersurfaces in ambient projective space times `Spec S`. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusTwoCubicFibreIso :
    pullback (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≅
      pullback
        (prod.lift
          (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
          (hypersurfaceToBase (a.map b) (ha.map b)))
        (prod.lift
          (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
          (hypersurfaceToBase q hq)) := by
  let eX := fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs
  let eY := relativeEquationFieldFibreIso h b s q hq j hj heq
  let f₀ := prod.lift
    (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
    (pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s)
  let g₀ := prod.lift
    (pullback.fst (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h) ≫
      projectiveUniversalToAmbient K (Fin 4) 3)
    (pullback.snd (projectiveUniversalToBase K (Fin 4) 3) (s ≫ h))
  let f := prod.lift
    (hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b)
    (hypersurfaceToBase (a.map b) (ha.map b))
  let g := prod.lift
    (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b)
    (hypersurfaceToBase q hq)
  have hf : f₀ = eX.hom ≫ f := by
    apply prod.hom_ext
    · simp only [Category.assoc, f₀, f, prod.lift_fst]
      exact (fixedCubicSurfaceFamilyFieldFibreIso_toAmbient a ha k b s hs).symm
    · simp only [Category.assoc, f₀, f, prod.lift_snd]
      exact (fixedCubicSurfaceFamilyFieldFibreIso_toField a ha k b s hs).symm
  have hg : g₀ = eY.hom ≫ g := by
    apply prod.hom_ext
    · simp only [Category.assoc, g₀, g, prod.lift_fst]
      exact (relativeEquationFieldFibreIso_toAmbient h b s q hq j hj heq).symm
    · simp only [Category.assoc, g₀, g, prod.lift_snd]
      exact (relativeEquationFieldFibreIso_toField h b s q hq j hj heq).symm
  exact fixedCubicSurfaceEquationZeroLocusFieldIncidenceIso a ha k h s ≪≫
    pullbackTransportIso eX eY f g f₀ g₀ hf hg

end PfaffianDescent
