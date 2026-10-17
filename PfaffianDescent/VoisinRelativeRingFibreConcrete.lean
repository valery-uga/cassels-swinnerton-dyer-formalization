import PfaffianDescent.VoisinRelativeFieldFibreIncidence
import PfaffianDescent.NormalizedUniversalEquationRingFibre

/-!
# Fixed-cubic fibre projections over arbitrary coefficient rings

The existing field-fibre comparison for the fixed cubic uses only the
coefficient-ring structure. Its projection compatibilities are recorded
here without a field assumption on the target ring, so they can be paired
with the normalized universal-equation fibre over local parameter rings.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K T : Type u} [Field K] [CommRing T]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (b : K →+* T) (s : Spec (.of T) ⟶ E)
  (hs : s ≫ k = Spec.map (CommRingCat.ofHom b))

/-- The arbitrary-ring fixed-cubic fibre comparison retains the parameter
point in `Spec T`. -/
theorem fixedCubicSurfaceFamilyRingFibreIso_toBase :
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

/-- The arbitrary-ring fixed-cubic fibre comparison retains its point in
ambient projective three-space after coefficient change. -/
theorem fixedCubicSurfaceFamilyRingFibreIso_toAmbient :
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

end PfaffianDescent
