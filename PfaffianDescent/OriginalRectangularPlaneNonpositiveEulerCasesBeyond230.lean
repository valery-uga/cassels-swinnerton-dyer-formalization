import PfaffianDescent.CorayActualPlaneSectionNonzeroEuler172
import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension

/-! The original172 nonzero-section bound gives section-free consequences
for negative and zero native Euler number on the SAME rectangular curve.
These cases require no positive-Euler boundary or H1-vanishing argument. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Negative native Euler number forces every actual section to vanish.
No section or section-space conclusion is supplied to the caller. -/
theorem smoothCubic_actualPlane_negativeEuler_topSections_subsingleton_beyond230
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let F := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
    let X := scheme (equationIdeal pE hpE)
    let pi := hypersurfaceToBase pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    ∀ M : X.Modules, schemeModuleLocallyRankOne M →
      (Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X M 1) < 0 →
      Subsingleton (SchemeModuleOpenSectionsOver pi M ⊤) := by
  classical
  dsimp only
  let F := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  let X := scheme (equationIdeal pE hpE)
  let pi := hypersurfaceToBase pE hpE
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  intro M hM hNegative
  have hSectionZero : ∀ s : M.val.obj (op ⊤), s = 0 := by
    intro s
    by_contra hs
    have hNonnegative :=
      (smoothCubic_actualPlane_nonzeroRankOneSection_finite_nonnegativeEuler_zeroEuler_rank_le_one172
        p hp hp0 M hM s hs).2.2.1
    have hNonnegative' : 0 ≤
        (Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank F (schemeModuleCohomology X M 1) := hNonnegative
    exact (not_le_of_gt hNegative) hNonnegative'
  exact ⟨fun s t => (hSectionZero s).trans (hSectionZero t).symm⟩

/-- Zero native Euler gives H0 rank at most one even when a nonzero section
has not been supplied. H1 vanishing is not asserted. -/
theorem smoothCubic_actualPlane_zeroEuler_topSections_finrank_le_one_beyond230
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let F := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
    let X := scheme (equationIdeal pE hpE)
    let pi := hypersurfaceToBase pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    ∀ M : X.Modules, schemeModuleLocallyRankOne M →
      (Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X M 1) = 0 →
      Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) ≤ 1 := by
  classical
  dsimp only
  let F := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  let X := scheme (equationIdeal pE hpE)
  let pi := hypersurfaceToBase pE hpE
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  intro M hM hZero
  by_cases hRankZero : Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) = 0
  · exact hRankZero.le.trans (Nat.zero_le 1)
  · have hRankPos : 0 < Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) := Nat.pos_of_ne_zero hRankZero
    letI : Nontrivial (SchemeModuleOpenSectionsOver pi M ⊤) :=
      Module.nontrivial_of_finrank_pos hRankPos
    obtain ⟨s, hs⟩ := exists_ne (0 : SchemeModuleOpenSectionsOver pi M ⊤)
    exact (smoothCubic_actualPlane_nonzeroRankOneSection_finite_nonnegativeEuler_zeroEuler_rank_le_one172
      p hp hp0 M hM s hs).2.2.2 hZero

end PfaffianDescent.Coray
