import PfaffianDescent.CorayWholePlaneSchemeIso
import PfaffianDescent.CorayWholeGenericCutImmersion

/-! Whole plane ideal transport. SAME literal whole cut becomes a literal
Fin3 homogeneous ideal via the actual graded substitution. Constructed scheme
isomorphism and actual graded-map identities compare its canonical immersion
with152's immersion into SAME149 E. No scheme/Cartier comparison premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def wholeGenericCutPlaneIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 3) (GenericHyperplaneField K)) :=
  wholePlaneRestrictionIdeal (genericHyperplaneCoefficient (K := K)) (wholeGenericCutIdeal C)

theorem wholeGenericCutPlaneIdeal_toIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    (wholeGenericCutPlaneIdeal C).toIdeal = (wholeGenericCutIdeal C).toIdeal.map
      (planeHyperplaneRestrictionHom (genericHyperplaneCoefficient (K := K))).toRingHom := rfl

theorem wholeGenericCut_contains_planeRelation
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    Ideal.span ({planeHyperplaneRelation (genericHyperplaneCoefficient (K := K))} :
      Set (MvPolynomial (Fin 4) (GenericHyperplaneField K))) ≤ (wholeGenericCutIdeal C).toIdeal := by
  change (equationIdeal (genericHyperplaneEquation (K := K))
    genericHyperplaneEquation_isHomogeneous).toIdeal ≤ (wholeGenericCutIdeal C).toIdeal
  exact le_sup_right

def wholeGenericCutPlaneSchemeIso
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    scheme (wholeGenericCutPlaneIdeal C) ≅ scheme (wholeGenericCutIdeal C) :=
  wholePlaneSchemeIso _ _ (wholeGenericCut_contains_planeRelation C)

theorem wholeGenericCutPlaneSchemeIso_toBase
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    (wholeGenericCutPlaneSchemeIso C).hom ≫ toBase (wholeGenericCutIdeal C) =
      toBase (wholeGenericCutPlaneIdeal C) :=
  wholePlaneSchemeIso_hom_toBase _ _ (wholeGenericCut_contains_planeRelation C)

theorem genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)).toIdeal ≤
      (wholeGenericCutPlaneIdeal C).toIdeal := by
  apply Ideal.span_le.mpr
  intro f hf
  obtain rfl := Set.mem_singleton_iff.mp hf
  rw [wholeGenericCutPlaneIdeal_toIdeal]
  have hpWhole : p.map (algebraMap K (GenericHyperplaneField K)) ∈ (wholeGenericCurveIdeal C).toIdeal := by
    rw [wholeGenericCurveIdeal_toIdeal]
    exact Ideal.mem_map_of_mem _ hpC
  have hpCut : p.map (algebraMap K (GenericHyperplaneField K)) ∈ (wholeGenericCutIdeal C).toIdeal :=
    (show (wholeGenericCurveIdeal C).toIdeal ≤ (wholeGenericCutIdeal C).toIdeal from le_sup_left) hpWhole
  exact Ideal.mem_map_of_mem _ hpCut

def wholeGenericCutPlaneIdealImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    scheme (wholeGenericCutPlaneIdeal C) ⟶
      hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp) :=
  PfaffianDescent.schemeQuotientMap _ _
    (genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal C p hp hpC)

instance wholeGenericCutPlaneIdealImmersion_isClosedImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    IsClosedImmersion (wholeGenericCutPlaneIdealImmersion C p hp hpC) :=
  PfaffianDescent.schemeQuotientMap_closedImmersion _ _ _

/-- Both paths use the literal SAME substitution on actual homogeneous
coordinate representatives, including every whole-cut nilpotent relation. -/
theorem wholeGenericCutPlaneSchemeIso_pair_triangle
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    (wholeGenericCutPlaneSchemeIso C).hom ≫ wholeGenericCutPairImmersion C p hp hpC =
      wholeGenericCutPlaneIdealImmersion C p hp hpC ≫ (genericPlaneCubicPairSchemeIso p hp).hom := by
  let t := genericHyperplaneCoefficient (K := K)
  let I := wholeGenericCutIdeal C
  let D := wholeGenericCutPlaneIdeal C
  let P := genericPlaneSectionPairIdeal p hp
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let W := wholePlaneGradedRestriction t I
  let Q := PfaffianDescent.gradedQuotientMap P I (genericPlanePairIdeal_le_wholeGenericCut C p hp hpC)
  let T := PfaffianDescent.gradedQuotientMap E D (genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal C p hp hpC)
  let F := planeSectionGradedRestriction t
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)
  have hcomp : W.comp Q = T.comp F := by
    apply GradedRingHom.ext
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change wholePlaneQuotientRestriction t I (Ideal.Quotient.mk I.toIdeal f) =
      PfaffianDescent.coordinateQuotientMap E D
        (genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal C p hp hpC)
        (Ideal.Quotient.mk E.toIdeal (planeHyperplaneRestrictionHom t f))
    rw [wholePlaneQuotientRestriction_mk, PfaffianDescent.coordinateQuotientMap_mk]
    rfl
  let hW := PfaffianDescent.gradedSurjective_irrelevant_le W
    (wholePlaneGradedRestriction_surjective t I (wholeGenericCut_contains_planeRelation C))
  let hQ := PfaffianDescent.gradedSurjective_irrelevant_le Q
    (PfaffianDescent.gradedQuotientMap_surjective _ _ _)
  let hT := PfaffianDescent.gradedSurjective_irrelevant_le T
    (PfaffianDescent.gradedQuotientMap_surjective _ _ _)
  let hF := PfaffianDescent.gradedSurjective_irrelevant_le F
    (planeSectionGradedRestriction_surjective _ _ _)
  change Proj.map W hW ≫ Proj.map Q hQ = Proj.map T hT ≫ Proj.map F hF
  exact (Proj.map_comp Q W hQ hW).symm.trans
    ((quotientProjMap_congr P D (W.comp Q) (T.comp F)
      (HomogeneousIdeal.irrelevant_le_map_comp hQ hW)
      (HomogeneousIdeal.irrelevant_le_map_comp hF hT) hcomp).trans
      (Proj.map_comp F T hF hT))

/-- Constructed comparison of literal SAME F with SAME actual149 rectangular
E, through the two already constructed151 SAME-pair comparisons. -/
def genericPlaneCubicToActualSectionIso
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp) ≅
      PfaffianDescent.linearHypersurfaceSection (genericPlaneInclusionMatrix (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) :=
  (genericPlaneCubicPairSchemeIso p hp).trans (actualGenericPlanePairSchemeIso p hp).symm

def wholeGenericCutPlaneIdealToSameE
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    scheme (wholeGenericCutPlaneIdeal C) ⟶
      PfaffianDescent.linearHypersurfaceSection (genericPlaneInclusionMatrix (K := K))
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) :=
  wholeGenericCutPlaneIdealImmersion C p hp hpC ≫ (genericPlaneCubicToActualSectionIso p hp).hom

instance wholeGenericCutPlaneIdealToSameE_isClosedImmersion
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    IsClosedImmersion (wholeGenericCutPlaneIdealToSameE C p hp hpC) := by
  unfold wholeGenericCutPlaneIdealToSameE
  infer_instance

/- Two bounded categorical proofs. Neither unfolds any actual scheme/Proj map. -/
private theorem wholePlanePairTriangle_postcomposeIso
    {𝒞 : Type*} [Category 𝒞] {D Z F P E : 𝒞}
    (a : D ⟶ Z) (b : Z ⟶ P) (c : D ⟶ F)
    (eFP : F ≅ P) (eEP : E ≅ P)
    (h : a ≫ b = c ≫ eFP.hom) :
    a ≫ (b ≫ eEP.inv) = c ≫ (eFP.trans eEP.symm).hom := by
  exact (Category.assoc a b eEP.inv).symm.trans
    ((congrArg (fun k => k ≫ eEP.inv) h).trans
      (Category.assoc c eFP.hom eEP.inv))

private theorem wholePlaneTriangle_originalCubic
    {𝒞 : Type*} [Category 𝒞] {D Z E S : 𝒞}
    (a : D ⟶ Z) (b : Z ⟶ E) (c : D ⟶ E)
    (f : E ⟶ S) (g : Z ⟶ S)
    (h : a ≫ b = c) (hbg : b ≫ f = g) :
    c ≫ f = a ≫ g := by
  exact (congrArg (fun k => k ≫ f) h.symm).trans
    ((Category.assoc a b f).trans (congrArg (fun k => a ≫ k) hbg))

/-- Exact actual WHOLE-Z immersion compatibility into SAME E. -/
theorem wholeGenericCutPlaneSchemeIso_sameE_triangle
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    (wholeGenericCutPlaneSchemeIso C).hom ≫ wholeGenericCutPlaneImmersion C p hp hpC =
      wholeGenericCutPlaneIdealToSameE C p hp hpC := by
  exact wholePlanePairTriangle_postcomposeIso
    (wholeGenericCutPlaneSchemeIso C).hom
    (wholeGenericCutPairImmersion C p hp hpC)
    (wholeGenericCutPlaneIdealImmersion C p hp hpC)
    (genericPlaneCubicPairSchemeIso p hp)
    (actualGenericPlanePairSchemeIso p hp)
    (wholeGenericCutPlaneSchemeIso_pair_triangle C p hp hpC)

theorem wholeGenericCutPlaneIdealToSameE_originalCubic
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hpC : p ∈ C.toIdeal) :
    wholeGenericCutPlaneIdealToSameE C p hp hpC ≫ actualGenericPlaneSectionImmersion p hp =
      (wholeGenericCutPlaneSchemeIso C).hom ≫ wholeGenericCutOriginalCubicImmersion C p hp hpC := by
  exact wholePlaneTriangle_originalCubic
    (wholeGenericCutPlaneSchemeIso C).hom
    (wholeGenericCutPlaneImmersion C p hp hpC)
    (wholeGenericCutPlaneIdealToSameE C p hp hpC)
    (actualGenericPlaneSectionImmersion p hp)
    (wholeGenericCutOriginalCubicImmersion C p hp hpC)
    (wholeGenericCutPlaneSchemeIso_sameE_triangle C p hp hpC)
    (wholeGenericCutPlaneImmersion_originalCubic C p hp hpC)

end PfaffianDescent.Coray
