import AllCharacteristics.HypersurfaceCoefficientNaturality

/-!
# Hypersurface maps under coefficient changes up to a unit

If coefficient change takes one homogeneous equation to a unit multiple of
another, it induces a canonical map of actual projective hypersurfaces. The
map is a base-change projection, with an explicit fiber isomorphism compatible
with both projections.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (b : R →+* S) (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
variable (p : MvPolynomial σ S) (hp : p.IsHomogeneous d) (a : S) (ha : IsUnit a)
variable (he : q.map b = C a * p)

include ha he in
/-- Coefficient change to a unit multiple gives the same homogeneous ideal. -/
theorem equationIdeal_map_of_unit_multiple :
    (equationIdeal q hq).toIdeal.map (MvPolynomial.map b) = (equationIdeal p hp).toIdeal :=
  (equationIdeal_map_of_eq b q hq (C a * p) (hp.C_mul a) he).trans
    (congrArg HomogeneousIdeal.toIdeal (equationIdeal_C_mul_of_isUnit a ha p hp))

/-- The canonical actual hypersurface map for coefficient change up to a unit. -/
noncomputable def scaledHypersurfaceMap : hypersurface p hp ⟶ hypersurface q hq :=
  projectiveCoefficientMap b (equationIdeal q hq) (equationIdeal p hp)
    (equationIdeal_map_of_unit_multiple b q hq p hp a ha he)

/-- The scaled coefficient map is the reduction map preceded by inverse unit scaling. -/
theorem scaling_inv_comp_reductionMap :
    (hypersurfaceScalingIso a ha p hp).inv ≫
      hypersurfaceReductionMap b q hq (C a * p) (hp.C_mul a) he =
    scaledHypersurfaceMap b q hq p hp a ha he := by
  let I := equationIdeal q hq
  let J := equationIdeal (C a * p) (hp.C_mul a)
  let K := equationIdeal p hp
  have h₁ : I.toIdeal.map (MvPolynomial.map b) = J.toIdeal :=
    equationIdeal_map_of_eq b q hq (C a * p) (hp.C_mul a) he
  have h₂ : J.toIdeal.map (MvPolynomial.map (RingHom.id S)) = K.toIdeal :=
    (coefficientIdeal_id J).trans
      (congrArg HomogeneousIdeal.toIdeal (equationIdeal_C_mul_of_isUnit a ha p hp))
  have hs := hypersurfaceScalingIso_inv_eq_projectiveCoefficientMap a ha p hp
  have hr := hypersurfaceReductionMap_eq_projectiveCoefficientMap b q hq
    (C a * p) (hp.C_mul a) he
  have hc := projectiveCoefficientMap_comp b (RingHom.id S) I J K h₁ h₂
  have heq := projectiveCoefficientMap_congr ((RingHom.id S).comp b) b I K
    (coefficientIdeal_comp b (RingHom.id S) I J K h₁ h₂)
    (equationIdeal_map_of_unit_multiple b q hq p hp a ha he) (RingHom.id_comp b)
  exact (congrArg₂ (fun f g ↦ f ≫ g) hs hr).trans (hc.trans heq)

/-- The equation after unit rescaling defines the entire coefficient-changed fiber. -/
noncomputable def scaledHypersurfaceFiberIso :
    hypersurface p hp ≅ pullback (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b)) :=
  (hypersurfaceScalingIso a ha p hp).symm ≪≫
    hypersurfaceReductionIso b q hq (C a * p) (hp.C_mul a) he

/-- The first fiber projection is exactly the canonical scaled coefficient map. -/
theorem scaledHypersurfaceFiberIso_hom_fst :
    (scaledHypersurfaceFiberIso b q hq p hp a ha he).hom ≫
      pullback.fst (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b)) =
    scaledHypersurfaceMap b q hq p hp a ha he :=
  (Category.assoc (hypersurfaceScalingIso a ha p hp).inv
    (hypersurfaceReductionIso b q hq (C a * p) (hp.C_mul a) he).hom _).trans
      (scaling_inv_comp_reductionMap b q hq p hp a ha he)

/-- The second fiber projection preserves the new coefficient structure. -/
theorem scaledHypersurfaceFiberIso_hom_snd :
    (scaledHypersurfaceFiberIso b q hq p hp a ha he).hom ≫
      pullback.snd (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b)) =
    hypersurfaceToBase p hp := by
  let s := hypersurfaceScalingIso a ha p hp
  let e := hypersurfaceReductionIso b q hq (C a * p) (hp.C_mul a) he
  have hs := s.inv_comp_eq.mpr (hypersurfaceScalingIso_hom_toBase a ha p hp).symm
  have he := hypersurfaceReductionIso_hom_snd b q hq (C a * p) (hp.C_mul a) he
  exact (Category.assoc s.inv e.hom _).trans ((congrArg (fun f ↦ s.inv ≫ f) he).trans hs)

/-- The scaled coefficient map commutes with the structure maps to the coefficient spectra. -/
theorem scaledHypersurfaceMap_toBase :
    scaledHypersurfaceMap b q hq p hp a ha he ≫ hypersurfaceToBase q hq =
      hypersurfaceToBase p hp ≫ Spec.map (CommRingCat.ofHom b) :=
  projectiveCoefficientMap_toBase b (equationIdeal q hq) (equationIdeal p hp)
    (equationIdeal_map_of_unit_multiple b q hq p hp a ha he)

/-- A coefficient change up to a unit gives an actual Cartesian hypersurface square. -/
theorem isPullback_scaledHypersurfaceMap :
    IsPullback (scaledHypersurfaceMap b q hq p hp a ha he) (hypersurfaceToBase p hp)
      (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b)) :=
  IsPullback.of_iso_pullback ⟨scaledHypersurfaceMap_toBase b q hq p hp a ha he⟩
    (scaledHypersurfaceFiberIso b q hq p hp a ha he)
    (scaledHypersurfaceFiberIso_hom_fst b q hq p hp a ha he)
    (scaledHypersurfaceFiberIso_hom_snd b q hq p hp a ha he)

end HomogeneousProjective
end AllCharacteristics
