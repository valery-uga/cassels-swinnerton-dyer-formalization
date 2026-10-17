import PfaffianDescent.VoisinCubicPositiveGlobalSections
import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-!
# Literal cubic sections of a smooth cubic surface

The exact sequence `O → O(3) → i_* O_S(3)` and the proved vanishing
`H¹(P³,O)=0` show that every intrinsic cubic section is represented by a
homogeneous cubic. This supplies the degree-three section model needed
for the twisted Serre and fixed-conic section counts.
-/

noncomputable section

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry MvPolynomial
open AllCharacteristics HomogeneousProjective

universe u

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Restriction of ambient cubic sections, with the pushed-forward target
identified with the intrinsic section space of the surface. -/
noncomputable def cubicPositiveThreeRestrictionSections
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (positiveSheafOfModules PS 3).sections →
      (positiveSheafOfModules (grading (equationIdeal p hp)) 3).sections :=
  fun s => pushforwardModuleSectionsEquiv (hypersurfaceToAmbient p hp)
    (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
    (SheafOfModules.sectionsMap
      (hypersurfacePositiveTwistToPushforward p hp 3) s)

/-- The literal restriction of ambient cubic sections to a smooth cubic
surface is surjective. No extra vanishing hypothesis is retained. -/
theorem cubicPositiveThreeRestrictionSections_surjective_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules] :
    Function.Surjective (cubicPositiveThreeRestrictionSections K p hp) := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := by
    change IsDomain (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set _))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  let S := hypersurfaceCrossingTwistRestrictionSequence p hp 0 (by omega)
  haveI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₁ 1) := by
    change Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS 0) 1)
    exact (p3_negativeTwist_cohomology_one_and_two_subsingleton K 0).1
  have hcoh : Function.Surjective
      (schemeModuleCohomologyMap (Proj PS) S.g 0) :=
    schemeModuleCohomology_zero_map_surjective_of_one_subsingleton
      (Proj PS) S
      (hypersurfaceCrossingTwistRestrictionSequence_shortExact p hp hp0 0 (by omega))
  have hsurj : Function.Surjective (SheafOfModules.sectionsMap
      (hypersurfacePositiveTwistToPushforward p hp 3)) :=
    sectionsMap_surjective_of_schemeModuleCohomologyMap_zero
      (Proj PS) S.g hcoh
  let e := pushforwardModuleSectionsEquiv (hypersurfaceToAmbient p hp)
    (positiveSheafOfModules (grading (equationIdeal p hp)) 3)
  intro t
  obtain ⟨s, hs⟩ := hsurj (e.symm t)
  refine ⟨s, ?_⟩
  change e (SheafOfModules.sectionsMap
    (hypersurfacePositiveTwistToPushforward p hp 3) s) = t
  exact e.eq_symm_apply.mp hs

/-- Restriction sends a homogeneous cubic to the section of its class in
the surface's graded coordinate ring. -/
theorem cubicPositiveThreeRestrictionSections_positiveGlobalSection
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (q : PS 3) :
    cubicPositiveThreeRestrictionSections K p hp
      (positiveGlobalSectionOfHomogeneous PS 3 q) =
      positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 3
        ⟨(quotientGradedRingHom (equationIdeal p hp)) q,
          (quotientGradedRingHom (equationIdeal p hp)).map_mem q.property⟩ := by
  apply PresheafOfModules.sections_ext
  intro U
  apply Subtype.ext
  funext y
  change Localization.localRingHom _ _
      (quotientGradedRingHom (equationIdeal p hp)).toRingHom rfl
      (Localization.mk (q : MvPolynomial (Fin 4) K)
        ⟨1, Submonoid.one_mem _⟩) =
    Localization.mk
      ((quotientGradedRingHom (equationIdeal p hp))
        (q : MvPolynomial (Fin 4) K))
      ⟨1, Submonoid.one_mem _⟩
  exact localRingHom_mk_one _ _
    (quotientGradedRingHom (equationIdeal p hp)).toRingHom rfl
    (q : MvPolynomial (Fin 4) K)

/-- All literal `O_S(3)` sections of a nonzero smooth cubic come from the
degree-three graded coordinate piece. -/
theorem cubic_positiveThreeGlobalSectionOfHomogeneous_surjective_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules] :
    Function.Surjective
      (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 3) := by
  intro t
  obtain ⟨s, hs⟩ :=
    cubicPositiveThreeRestrictionSections_surjective_of_smooth K p hp hp0 t
  obtain ⟨q, hq⟩ :=
    p3_positiveGlobalSectionOfHomogeneous_surjective K 3 (by decide) s
  let qbar : grading (equationIdeal p hp) 3 :=
    ⟨(quotientGradedRingHom (equationIdeal p hp)) q,
      (quotientGradedRingHom (equationIdeal p hp)).map_mem q.property⟩
  refine ⟨qbar, ?_⟩
  calc
    positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 3 qbar =
        cubicPositiveThreeRestrictionSections K p hp
          (positiveGlobalSectionOfHomogeneous PS 3 q) :=
      (cubicPositiveThreeRestrictionSections_positiveGlobalSection K p hp q).symm
    _ = cubicPositiveThreeRestrictionSections K p hp s :=
      congrArg (cubicPositiveThreeRestrictionSections K p hp) hq
    _ = t := hs

set_option backward.isDefEq.respectTransparency false in
/-- The actual space of cubic-twist sections on a smooth cubic is linearly
equivalent to the degree-three part of its homogeneous coordinate ring. -/
noncomputable def cubicPositiveThreeGlobalSectionsLinearEquiv
    [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules] :
    grading (equationIdeal p hp) 3 ≃ₗ[K]
      SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3) := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := by
    change IsDomain (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set _))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  letI : Nonempty (scheme (equationIdeal p hp)) :=
    nonempty_hypersurface_of_nonzero_homogeneous_cubic_equation
      (by decide) p hp hp0
  exact LinearEquiv.ofBijective
    (positiveHomogeneousGlobalSectionLinearMap (equationIdeal p hp) 3)
    ⟨positiveHomogeneousGlobalSectionLinearMap_injective (equationIdeal p hp) 3,
      positiveHomogeneousGlobalSectionLinearMap_surjective (equationIdeal p hp) 3
        (cubic_positiveThreeGlobalSectionOfHomogeneous_surjective_of_smooth
          K p hp hp0)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The literal sheaf section space `H⁰(S,O_S(3))` has dimension nineteen. -/
theorem cubicPositiveThreeGlobalSections_finrank
    [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules] :
    Module.finrank K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) = 19 := by
  rw [← (cubicPositiveThreeGlobalSectionsLinearEquiv K p hp hp0).finrank_eq]
  exact cubicSurface_grade_three_finrank p hp hp0

end PfaffianDescent.ProjectiveNegativeTwist
