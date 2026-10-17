import PfaffianDescent.VoisinRelativeFieldFibreIncidence
import PfaffianDescent.PullbackSourceIso
import AllCharacteristics.HypersurfaceCoefficientNaturality
import AllCharacteristics.UniversalProjectiveEquationFiber

/-!
# Concrete hypersurfaces in the relative incidence field fibre

Projection compatibility for the two known field-fibre isomorphisms is
needed to transport the incidence intersection to explicit cubics.
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
  (b : K →+* S) (s : Spec (.of S) ⟶ E)
  (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))

/-- The fixed-surface field-fibre identification preserves the field point. -/
theorem fixedCubicSurfaceFamilyFieldFibreIso_toField :
    (fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs).hom ≫
      hypersurfaceToBase (a.map b) (ha.map b) =
    pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s := by
  unfold fixedCubicSurfaceFamilyFieldFibreIso
  rw [Iso.trans_hom, Iso.trans_hom]
  simp only [Category.assoc]
  rw [← hypersurfaceBaseChangeIso_hom_snd b a ha]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
  change (pullbackLeftPullbackSndIso (hypersurfaceToBase a ha) k s).hom ≫
    (pullback.congrHom rfl hs).hom ≫
      pullback.snd (hypersurfaceToBase a ha) (Spec.map (CommRingCat.ofHom b)) = _
  simp only [pullback.congrHom, asIso_hom, pullback.map,
    pullback.lift_snd]
  exact pullbackLeftPullbackSndIso_hom_snd (hypersurfaceToBase a ha) k s

/-- The same fibre comparison preserves the ambient projective point after
changing coefficients from `K` to `S`. -/
theorem fixedCubicSurfaceFamilyFieldFibreIso_toAmbient :
    (fixedCubicSurfaceFamilyFieldFibreIso a ha k b s hs).hom ≫
      hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b =
    pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
      pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha := by
  have hb : (hypersurfaceBaseChangeIso b a ha).hom ≫
      pullback.fst (hypersurfaceToBase a ha) (Spec.map (CommRingCat.ofHom b)) ≫
        hypersurfaceToAmbient a ha =
      hypersurfaceToAmbient (a.map b) (ha.map b) ≫ ambientCoefficientMap b := by
    rw [← Category.assoc, hypersurfaceBaseChangeIso_hom_fst]
    exact projectiveCoefficientMap_comp_quotientProjMap b
      (equationIdeal a ha) (equationIdeal (a.map b) (ha.map b))
      (equationIdeal_map b a ha)
  rw [← hb]
  unfold fixedCubicSurfaceFamilyFieldFibreIso
  rw [Iso.trans_hom, Iso.trans_hom]
  simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_assoc]
  change (pullbackLeftPullbackSndIso (hypersurfaceToBase a ha) k s).hom ≫
    (pullback.congrHom rfl hs).hom ≫
      pullback.fst (hypersurfaceToBase a ha) (Spec.map (CommRingCat.ofHom b)) ≫
        hypersurfaceToAmbient a ha = _
  simp only [pullback.congrHom, asIso_hom,
    pullback.map, pullback.lift_fst_assoc, Category.comp_id]
  simpa only [Category.assoc] using
    (congrArg (· ≫ hypersurfaceToAmbient a ha)
      (pullbackLeftPullbackSndIso_hom_fst (hypersurfaceToBase a ha) k s))

/-- The universal equation fibre isomorphism also preserves the ambient
point of its concrete cubic hypersurface after coefficient change. -/
theorem projectiveEquationFiberIso_toAmbient
    (q : MvPolynomial (Fin 4) S) (hq : q.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : q.coeff j.1 ≠ 0) :
    (projectiveEquationFiberIso b q j hj hq).hom ≫
      pullback.fst (projectiveUniversalToBase K (Fin 4) 3)
        (projectiveEquationParameter b q j hj) ≫
          projectiveUniversalToAmbient K (Fin 4) 3 =
      hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b := by
  rw [← Category.assoc, projectiveEquationFiberIso_hom_fst]
  exact projectiveEquationFiberToUniversalFamily_comp_toAmbient b q j hj hq

/-- The inverse fibre identification preserves the ambient point. -/
theorem projectiveEquationFiberIso_inv_toAmbient
    (q : MvPolynomial (Fin 4) S) (hq : q.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : q.coeff j.1 ≠ 0) :
    (projectiveEquationFiberIso b q j hj hq).inv ≫
      (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap b) =
    pullback.fst (projectiveUniversalToBase K (Fin 4) 3)
      (projectiveEquationParameter b q j hj) ≫
        projectiveUniversalToAmbient K (Fin 4) 3 := by
  rw [← projectiveEquationFiberIso_toAmbient b q hq j hj]
  simp only [Iso.inv_hom_id_assoc]

/-- The inverse fibre identification preserves the field point. -/
theorem projectiveEquationFiberIso_inv_toField
    (q : MvPolynomial (Fin 4) S) (hq : q.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : q.coeff j.1 ≠ 0) :
    (projectiveEquationFiberIso b q j hj hq).inv ≫
      hypersurfaceToBase q hq =
    pullback.snd (projectiveUniversalToBase K (Fin 4) 3)
      (projectiveEquationParameter b q j hj) := by
  rw [← projectiveEquationFiberIso_hom_snd b q j hj hq]
  simp only [Iso.inv_hom_id_assoc]

end PfaffianDescent
