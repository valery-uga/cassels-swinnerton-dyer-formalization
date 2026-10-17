import PfaffianDescent.CorayPlaneSectionGradedQuotient
import PfaffianDescent.HomogeneousQuotientMap

/-! SOURCE ONLY / UNVERIFIED151. The explicit inverse graded quotient maps
construct the actual SAME-Proj isomorphism and its exact original immersion
commutation. No scheme comparison or commutative square is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d)
local notation "I" => planeSectionHomogeneousIdeal t p hp
local notation "J" => equationIdeal (planeHyperplaneRestrictionHom t p)
  (planeHyperplaneRestrictionHom_homogeneous t p hp)

/-- Native isomorphism from the literal restricted plane hypersurface to the
actual four-variable homogeneous pair-ideal scheme. -/
def planeSectionSchemeIso :
    hypersurface (planeHyperplaneRestrictionHom t p)
      (planeHyperplaneRestrictionHom_homogeneous t p hp) ≅ scheme I := by
  change Proj (grading J) ≅ Proj (grading I)
  let F := planeSectionGradedRestriction t p hp
  let G := planeSectionGradedInclusion t p hp
  let hF := PfaffianDescent.gradedSurjective_irrelevant_le F
    (planeSectionGradedRestriction_surjective t p hp)
  let hG := PfaffianDescent.gradedSurjective_irrelevant_le G
    (planeSectionGradedInclusion_surjective t p hp)
  refine {
    hom := Proj.map F hF
    inv := Proj.map G hG
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · rw [← Proj.map_comp G F hG hF]
    have h : F.comp G = GradedRingHom.id (grading J) :=
      planeSectionGradedRestriction_comp_inclusion t p hp
    simpa only [h] using (Proj.map_id (𝒜 := grading J))
  · rw [← Proj.map_comp F G hF hG]
    have h : G.comp F = GradedRingHom.id (grading I) :=
      planeSectionGradedInclusion_comp_restriction t p hp
    simpa only [h] using (Proj.map_id (𝒜 := grading I))

/-- The actual pair ideal contains the original cubic equation ideal. -/
theorem planeSection_original_ideal_le : (equationIdeal p hp).toIdeal ≤ (I).toIdeal := by
  rw [planeSectionHomogeneousIdeal, HomogeneousIdeal.toIdeal_sup]
  exact le_sup_left

/-- The canonical original-cubic closed immersion defined by (p,H). -/
def planeSectionPairImmersion : scheme I ⟶ hypersurface p hp :=
  PfaffianDescent.schemeQuotientMap (equationIdeal p hp) I
    (planeSection_original_ideal_le t p hp)

instance planeSectionPairImmersion_isClosedImmersion :
    IsClosedImmersion (planeSectionPairImmersion t p hp) :=
  PfaffianDescent.schemeQuotientMap_closedImmersion _ _ _

/-- The same split substitution defines the direct plane-to-cubic immersion. -/
def planeSectionRestrictionImmersion :
    hypersurface (planeHyperplaneRestrictionHom t p)
      (planeHyperplaneRestrictionHom_homogeneous t p hp) ⟶ hypersurface p hp :=
  PfaffianDescent.polynomialProjectiveMap (equationIdeal p hp) J
    (planeHyperplaneRestrictionHom t)
    (by
      apply Ideal.span_le.mpr
      intro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      exact Ideal.subset_span (Set.mem_singleton _))
    (fun _ q hq => planeHyperplaneRestrictionHom_homogeneous t q hq)
    (planeHyperplaneRestrictionHom_surjective t)

/-- Actual SAME-Proj comparison commutes with the ORIGINAL immersion: both
paths are induced by the literal SAME polynomial substitution. -/
theorem planeSectionSchemeIso_hom_immersion :
    (planeSectionSchemeIso t p hp).hom ≫ planeSectionPairImmersion t p hp =
      planeSectionRestrictionImmersion t p hp := by
  let Q := PfaffianDescent.gradedQuotientMap (equationIdeal p hp) I
    (planeSection_original_ideal_le t p hp)
  let F := planeSectionGradedRestriction t p hp
  let D := PfaffianDescent.polynomialQuotientGradingMap (equationIdeal p hp) J
    (planeHyperplaneRestrictionHom t)
    (show (equationIdeal p hp).toIdeal ≤ (J).toIdeal.comap
        (planeHyperplaneRestrictionHom t).toRingHom from by
      apply Ideal.span_le.mpr
      intro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      exact Ideal.subset_span (Set.mem_singleton _))
    (fun _ q hq => planeHyperplaneRestrictionHom_homogeneous t q hq)
  have hcomp : F.comp Q = D := by
    apply GradedRingHom.ext
    intro x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    change PfaffianDescent.polynomialQuotientMap I J (planeHyperplaneRestrictionHom t)
      (planeSection_restriction_ideal_le t p hp) (Ideal.Quotient.mk (I).toIdeal q) = _
    rw [PfaffianDescent.polynomialQuotientMap_mk]
    rfl
  let hQ := PfaffianDescent.gradedSurjective_irrelevant_le Q
    (PfaffianDescent.gradedQuotientMap_surjective _ _ _)
  let hF := PfaffianDescent.gradedSurjective_irrelevant_le F
    (planeSectionGradedRestriction_surjective t p hp)
  change Proj.map F hF ≫ Proj.map Q hQ = _
  rw [← Proj.map_comp Q F hQ hF]
  have hD : Function.Surjective D :=
    PfaffianDescent.polynomialQuotientGradingMap_surjective _ _ _ _ _
      (planeHyperplaneRestrictionHom_surjective t)
  change Proj.map (F.comp Q) _ =
    Proj.map D (PfaffianDescent.gradedSurjective_irrelevant_le D hD)
  congr 1

/-- The SAME-Proj isomorphism preserves the actual coefficient structure map. -/
theorem planeSectionSchemeIso_hom_toBase :
    (planeSectionSchemeIso t p hp).hom ≫ toBase I =
      hypersurfaceToBase (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp) := by
  exact PfaffianDescent.polynomialProjectiveMap_toBase I J
    (planeHyperplaneRestrictionHom t) (planeSection_restriction_ideal_le t p hp)
    (fun _ q hq => planeHyperplaneRestrictionHom_homogeneous t q hq)
    (planeHyperplaneRestrictionHom_surjective t)

end PfaffianDescent.Coray

