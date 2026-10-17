import PfaffianDescent.CorayWholeGenericHyperplaneRegular
import PfaffianDescent.CorayActualGenericPlaneSectionSchemeIso

/-! SOURCE ONLY / UNVERIFIED152. Literal whole C_L+(H) is a native closed
subscheme of the SAME actual generic plane section E. Its original cubic
immersion commutes with both the E path and the whole C_L path. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal original equation remains in the literal whole extended ideal. -/
theorem originalEquation_mem_wholeGenericCurveIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hpC : p ∈ C.toIdeal) :
    p.map (algebraMap K (GenericHyperplaneField K)) ∈ (wholeGenericCurveIdeal C).toIdeal := by
  rw [wholeGenericCurveIdeal_toIdeal]
  exact Ideal.mem_map_of_mem _ hpC

/-- SAME (p_L,H) lies in SAME whole C_L+(H), derived from original containment. -/
theorem genericPlanePairIdeal_le_wholeGenericCut
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d) (hpC : p ∈ C.toIdeal) :
    (genericPlaneSectionPairIdeal p hp).toIdeal ≤ (wholeGenericCutIdeal C).toIdeal := by
  rw [genericPlaneSectionPairIdeal_toIdeal]
  apply Ideal.span_le.mpr
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · exact (show (wholeGenericCurveIdeal C).toIdeal ≤ (wholeGenericCutIdeal C).toIdeal
      from le_sup_left) (originalEquation_mem_wholeGenericCurveIdeal C p hpC)
  · exact (show (equationIdeal (genericHyperplaneEquation (K := K))
      genericHyperplaneEquation_isHomogeneous).toIdeal ≤ (wholeGenericCutIdeal C).toIdeal
      from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))

/-- The actual whole-cut canonical closed immersion into the SAME pair Proj. -/
def wholeGenericCutPairImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    scheme (wholeGenericCutIdeal C) ⟶ scheme (genericPlaneSectionPairIdeal p hp) :=
  PfaffianDescent.schemeQuotientMap _ _ (genericPlanePairIdeal_le_wholeGenericCut C p hp hpC)

instance wholeGenericCutPairImmersion_isClosedImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    IsClosedImmersion (wholeGenericCutPairImmersion C p hp hpC) :=
  PfaffianDescent.schemeQuotientMap_closedImmersion _ _ _

/-- The actual whole cut sits in the SAME native149 E, by the inverse of the
constructed151 comparison. No abstract E or comparison hypothesis is supplied. -/
def wholeGenericCutPlaneImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    scheme (wholeGenericCutIdeal C) ⟶
      PfaffianDescent.linearHypersurfaceSection (genericPlaneInclusionMatrix (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) :=
  wholeGenericCutPairImmersion C p hp hpC ≫ (actualGenericPlanePairSchemeIso p hp).inv

instance wholeGenericCutPlaneImmersion_isClosedImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    IsClosedImmersion (wholeGenericCutPlaneImmersion C p hp hpC) := by
  unfold wholeGenericCutPlaneImmersion
  infer_instance

/-- The direct canonical immersion into the original coefficient-extended cubic. -/
def wholeGenericCutOriginalCubicImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    scheme (wholeGenericCutIdeal C) ⟶
      hypersurface (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) :=
  PfaffianDescent.schemeQuotientMap _ _
    ((planeSection_original_ideal_le _ _ (hp.map _)).trans
      (genericPlanePairIdeal_le_wholeGenericCut C p hp hpC))

/-- Exact original immersion commutation, with SAME E and SAME original cubic. -/
theorem wholeGenericCutPlaneImmersion_originalCubic
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    wholeGenericCutPlaneImmersion C p hp hpC ≫ actualGenericPlaneSectionImmersion p hp =
      wholeGenericCutOriginalCubicImmersion C p hp hpC := by
  have htri : (actualGenericPlanePairSchemeIso p hp).inv ≫
      actualGenericPlaneSectionImmersion p hp = actualGenericPlanePairImmersion p hp := by
    rw [← actualGenericPlanePairSchemeIso_hom_immersion]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  unfold wholeGenericCutPlaneImmersion
  rw [Category.assoc, htri]
  exact PfaffianDescent.schemeQuotientMap_comp _ _ _ _ _ _

/-- The SAME whole original ideal is retained in the other canonical path. -/
def wholeGenericCutCurveImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    scheme (wholeGenericCutIdeal C) ⟶ scheme (wholeGenericCurveIdeal C) :=
  PfaffianDescent.schemeQuotientMap _ _ le_sup_left

/-- The whole-cut map is over the actual generic parameter field. -/
theorem wholeGenericCutPairImmersion_toBase
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    wholeGenericCutPairImmersion C p hp hpC ≫ toBase (genericPlaneSectionPairIdeal p hp) =
      toBase (wholeGenericCutIdeal C) :=
  PfaffianDescent.schemeQuotientMap_toBase _ _ _

end PfaffianDescent.Coray
