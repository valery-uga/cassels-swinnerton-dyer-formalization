import AllCharacteristics.HypersurfaceReduction
import AllCharacteristics.HypersurfaceScaling
import AllCharacteristics.ProjectiveCoefficientComposition
import AllCharacteristics.HomogeneousProjectiveAmbient

/-!
# Naturality of hypersurface reduction and scaling

The exact reduction map and the isomorphism from scaling by a unit are the
canonical projective coefficient morphisms. These identifications connect the
constructed family-overlap isomorphisms to the proved composition identities.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equal homogeneous equations have equal actual homogeneous ideals. -/
theorem equationIdeal_congr (p q : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) (h : p = q) :
    equationIdeal p hp = equationIdeal q hq := by
  subst q
  rfl

/-- A specified reduced equation has exactly the coefficient-changed ideal. -/
theorem equationIdeal_map_of_eq (b : R →+* S)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ S) (hp : p.IsHomogeneous d) (he : q.map b = p) :
    (equationIdeal q hq).toIdeal.map (MvPolynomial.map b) = (equationIdeal p hp).toIdeal := by
  subst p
  exact equationIdeal_map b q hq

/-- Equal coefficient homomorphisms induce equal projective morphisms. -/
theorem projectiveCoefficientMap_congr (f g : R →+* S)
    (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    (J : HomogeneousIdeal (homogeneousSubmodule σ S))
    (hf : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
    (hg : I.toIdeal.map (MvPolynomial.map g) = J.toIdeal) (h : f = g) :
    projectiveCoefficientMap f I J hf = projectiveCoefficientMap g I J hg := by
  subst g
  rfl

/-- Identity coefficient change between equal homogeneous ideals is their
canonical scheme identification. -/
theorem projectiveCoefficientMap_id_eqToHom
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) (h : I = J) :
    projectiveCoefficientMap (RingHom.id R) I J
      ((coefficientIdeal_id I).trans (congrArg HomogeneousIdeal.toIdeal h)) =
      eqToHom (congrArg scheme h.symm) := by
  subst J
  exact projectiveCoefficientMap_id I

/-- The first projection of hypersurface base change is the canonical projective
coefficient morphism. -/
theorem hypersurfaceBaseChangeIso_hom_fst (b : R →+* S)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d) :
    (hypersurfaceBaseChangeIso b q hq).hom ≫
      pullback.fst (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b)) =
    projectiveCoefficientMap b (equationIdeal q hq) (equationIdeal (q.map b) (hq.map b))
      (equationIdeal_map b q hq) :=
  projectiveBaseChangeIso_hom_fst _ _ _ _

/-- The exact reduction inclusion is the canonical projective coefficient map. -/
theorem hypersurfaceReductionMap_eq_projectiveCoefficientMap (b : R →+* S)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ S) (hp : p.IsHomogeneous d) (he : q.map b = p) :
    hypersurfaceReductionMap b q hq p hp he =
      projectiveCoefficientMap b (equationIdeal q hq) (equationIdeal p hp)
        (equationIdeal_map_of_eq b q hq p hp he) := by
  subst p
  exact hypersurfaceBaseChangeIso_hom_fst b q hq

/-- The ambient projective map of an exact hypersurface reduction is obtained
by changing coefficients in the ambient projective space. -/
theorem hypersurfaceReductionMap_comp_hypersurfaceToAmbient (b : R →+* S)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ S) (hp : p.IsHomogeneous d) (he : q.map b = p) :
    hypersurfaceReductionMap b q hq p hp he ≫ hypersurfaceToAmbient q hq =
      hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b := by
  rw [hypersurfaceReductionMap_eq_projectiveCoefficientMap b q hq p hp he]
  exact projectiveCoefficientMap_comp_quotientProjMap b (equationIdeal q hq)
    (equationIdeal p hp) (equationIdeal_map_of_eq b q hq p hp he)

/-- Unit scaling is the canonical identity coefficient map between the equal ideals. -/
theorem hypersurfaceScalingIso_hom_eq_projectiveCoefficientMap
    (a : R) (ha : IsUnit a) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    (hypersurfaceScalingIso a ha p hp).hom =
      projectiveCoefficientMap (RingHom.id R) (equationIdeal p hp)
        (equationIdeal (C a * p) (hp.C_mul a))
        ((coefficientIdeal_id (equationIdeal p hp)).trans
          (congrArg HomogeneousIdeal.toIdeal (equationIdeal_C_mul_of_isUnit a ha p hp).symm)) :=
  (projectiveCoefficientMap_id_eqToHom (equationIdeal p hp)
    (equationIdeal (C a * p) (hp.C_mul a)) (equationIdeal_C_mul_of_isUnit a ha p hp).symm).symm

/-- The inverse unit-scaling map has the opposite canonical coefficient-map description. -/
theorem hypersurfaceScalingIso_inv_eq_projectiveCoefficientMap
    (a : R) (ha : IsUnit a) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    (hypersurfaceScalingIso a ha p hp).inv =
      projectiveCoefficientMap (RingHom.id R) (equationIdeal (C a * p) (hp.C_mul a))
        (equationIdeal p hp)
        ((coefficientIdeal_id (equationIdeal (C a * p) (hp.C_mul a))).trans
          (congrArg HomogeneousIdeal.toIdeal (equationIdeal_C_mul_of_isUnit a ha p hp))) :=
  (projectiveCoefficientMap_id_eqToHom (equationIdeal (C a * p) (hp.C_mul a))
    (equationIdeal p hp) (equationIdeal_C_mul_of_isUnit a ha p hp)).symm

/-- The inverse scaling identification is ambiently the identity coefficient
change between the two projective hypersurfaces. -/
theorem hypersurfaceScalingIso_inv_comp_hypersurfaceToAmbient
    (a : R) (ha : IsUnit a) (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (hypersurfaceScalingIso a ha p hp).inv ≫
      hypersurfaceToAmbient (MvPolynomial.C a * p) (hp.C_mul a) =
        hypersurfaceToAmbient p hp ≫ ambientCoefficientMap (RingHom.id R) := by
  rw [hypersurfaceScalingIso_inv_eq_projectiveCoefficientMap a ha p hp]
  exact projectiveCoefficientMap_comp_quotientProjMap (RingHom.id R)
    (equationIdeal (MvPolynomial.C a * p) (hp.C_mul a)) (equationIdeal p hp) _

end HomogeneousProjective
end AllCharacteristics
