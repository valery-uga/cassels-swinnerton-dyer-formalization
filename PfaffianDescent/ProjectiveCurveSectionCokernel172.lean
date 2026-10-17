import PfaffianDescent.SchemeModuleNonzeroTopSectionGenericStalk
import PfaffianDescent.CorayRankOneSectionCokernelClosedSupport
import PfaffianDescent.CorayIntegralCurveClosedSupportFinite
import PfaffianDescent.SchemeModuleUnitHomCokernelFinitePresentation
import PfaffianDescent.SchemeModuleQuasicoherentClosedSupportH1Vanishing
import AllCharacteristics.ProjectiveCommonAffineNeighborhood

/-! SOURCE ONLY172. The actual nonzero-section cokernel on the original
projective integral curve has finite closed support and zero intrinsic H1.
No signed word, normalization, support certificate or duality input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective MvPolynomial
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Nonzero-section geometry on the SAME original integral Noetherian
curve, for an arbitrary locally rank-one coefficient. The actual generic
frame is chosen from local rank one, rather than given by a signed word. -/
theorem integralCurve_nonzeroRankOneSection_cokernel_support_finite_closed
    (X : Scheme.{u}) [IsIntegral X] [NoetherianSpace X]
    (pi : X ⟶ Spec (.of K))
    (hdim : ∀ x : X, Ring.DimensionLEOne (X.presheaf.stalk x))
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    let Q := cokernel (schemeModuleTopSectionHom M s)
    IsClosed (schemeModuleStalkSupport Q) ∧
      (schemeModuleStalkSupport Q).Finite ∧
      ∀ x ∈ schemeModuleStalkSupport Q, IsClosed ({x} : Set X) := by
  classical
  obtain ⟨U, hgU, ⟨eU⟩⟩ := hM (genericPoint X)
  let Q := (show X.Modules from cokernel (schemeModuleTopSectionHom M s))
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    schemeModuleUnitHom_cokernel_stalkSupport_isClosed M hM (schemeModuleTopSectionHom M s)
  have hz := schemeModuleTopSectionHom_cokernel_genericStalk_isZero pi M hM U hgU eU s hs
  have hgeneric : Subsingleton ((Scheme.Modules.presheaf (X := X) Q).stalk
      (genericPoint X)) := ModuleCat.subsingleton_of_isZero hz
  have hg : genericPoint X ∉ schemeModuleStalkSupport Q := by
    change ¬ Nontrivial ((Scheme.Modules.presheaf (X := X) Q).stalk (genericPoint X))
    exact not_nontrivial_iff_subsingleton.mpr hgeneric
  exact ⟨hclosed, integralCurve_closed_avoiding_generic_finite_and_closedPoints
    X hdim (schemeModuleStalkSupport Q) hclosed hg⟩

/-- The SAME actual section cokernel has zero H1. Projectivity puts its
own finite support in a common affine open; native quasicoherence and the
accepted supported cohomology contraction then give vanishing. -/
theorem projectiveIntegralCurve_nonzeroRankOneSection_cokernel_hOne_zero
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 3) K))
    [IsIntegral (scheme I)]
    (hdim : ∀ x : scheme I, Ring.DimensionLEOne ((scheme I).presheaf.stalk x))
    (M : (scheme I).Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    let X := scheme I
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    Subsingleton (schemeModuleCohomology X (cokernel (schemeModuleTopSectionHom M s)) 1) := by
  classical
  let X := scheme I
  let pi := toBase I
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pi
  letI : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  let Q := (show X.Modules from cokernel (schemeModuleTopSectionHom M s))
  letI : Q.IsQuasicoherent :=
    schemeModuleUnitHom_cokernel_isQuasicoherent M hM (schemeModuleTopSectionHom M s)
  obtain ⟨hclosed, hfinite, _hpoints⟩ :=
    integralCurve_nonzeroRankOneSection_cokernel_support_finite_closed X pi hdim M hM s hs
  obtain ⟨U, hU⟩ := AllCharacteristics.exists_affineOpen_containing_projective_finset
    (grading I) hfinite.toFinset
  have hsU : ∀ x ∈ schemeModuleStalkSupport Q, x ∈ U.1 := by
    intro x hx
    exact hU x (hfinite.mem_toFinset.mpr hx)
  exact schemeModule_quasicoherent_cohomology_one_subsingleton_of_closedSupport_subset_affine
    pi Q hclosed U.1 U.2 hsU

end PfaffianDescent.Coray
