import PfaffianDescent.CorayWholePlaneGradedQuotient


/-! SOURCE ONLY / UNVERIFIED155. Actual inverse whole-ideal graded maps
construct the actual whole-cut scheme comparison. A bounded native congruence
helper handles dependent irrelevant-cover proofs without a large rewrite. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Native Proj maps induced by equal actual graded maps are equal; the
irrelevant-cover witnesses are propositions and do not alter the morphism. -/
theorem quotientProjMap_congr
    {σ τ : Type} (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    (J : HomogeneousIdeal (homogeneousSubmodule τ R))
    (f g : grading I →+*ᵍ grading J)
    (hf : HomogeneousIdeal.irrelevant (grading J) ≤ (HomogeneousIdeal.irrelevant (grading I)).map f)
    (hg : HomogeneousIdeal.irrelevant (grading J) ≤ (HomogeneousIdeal.irrelevant (grading I)).map g)
    (hfg : f = g) : Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

/-- The literal ENTIRE homogeneous ideal and its literal three-variable
image define isomorphic schemes, from actual inverse graded maps. -/
def wholePlaneSchemeIso
    (t : Fin 3 → R) (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hH : Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) R)) ≤ I.toIdeal) :
    scheme (wholePlaneRestrictionIdeal t I) ≅ scheme I := by
  let D := wholePlaneRestrictionIdeal t I
  change Proj (grading D) ≅ Proj (grading I)
  let F := wholePlaneGradedRestriction t I
  let G := wholePlaneGradedInclusion t I hH
  let hF := PfaffianDescent.gradedSurjective_irrelevant_le F
    (wholePlaneGradedRestriction_surjective t I hH)
  let hG := PfaffianDescent.gradedSurjective_irrelevant_le G
    (wholePlaneGradedInclusion_surjective t I hH)
  refine { hom := Proj.map F hF
           inv := Proj.map G hG
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · rw [← Proj.map_comp G F hG hF]
    exact (quotientProjMap_congr D D (F.comp G) (GradedRingHom.id (grading D))
      (HomogeneousIdeal.irrelevant_le_map_comp hG hF) (by simp)
      (wholePlaneGradedRestriction_comp_inclusion t I hH)).trans (Proj.map_id (𝒜 := grading D))
  · rw [← Proj.map_comp F G hF hG]
    exact (quotientProjMap_congr I I (G.comp F) (GradedRingHom.id (grading I))
      (HomogeneousIdeal.irrelevant_le_map_comp hF hG) (by simp)
      (wholePlaneGradedInclusion_comp_restriction t I hH)).trans (Proj.map_id (𝒜 := grading I))

theorem wholePlaneSchemeIso_hom_toBase
    (t : Fin 3 → R) (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hH : Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) R)) ≤ I.toIdeal) :
    (wholePlaneSchemeIso t I hH).hom ≫ toBase I = toBase (wholePlaneRestrictionIdeal t I) := by
  exact PfaffianDescent.polynomialProjectiveMap_toBase I (wholePlaneRestrictionIdeal t I)
    (planeHyperplaneRestrictionHom t) (wholePlane_restriction_ideal_le t I)
    (fun _ q hq => planeHyperplaneRestrictionHom_homogeneous t q hq)
    (planeHyperplaneRestrictionHom_surjective t)

end PfaffianDescent.Coray
