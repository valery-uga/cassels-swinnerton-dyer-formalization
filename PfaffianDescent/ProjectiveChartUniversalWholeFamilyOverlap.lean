import PfaffianDescent.ProjectivePositiveHomogeneousChartWholeTransition

/-! Derived matching of the original chart universal WHOLE families on
the actual parameter overlap and every further scheme test. The actual
transition and universal families are existing constructions; no matching
or source-comparison outcome is a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u v w
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Abstract contravariant type-functor composition, before any concrete
geometric family or universal point is substituted. -/
private theorem actualContravariantTypeFunctor_map_comp_apply001
    {C : Type v} [Category.{w} C] (A : Cᵒᵖ ⥤ Type u)
    {T W V : C} (g : T ⟶ W) (t : W ⟶ V) (P : A.obj (.op V)) :
    A.map (g ≫ t).op P = A.map g.op (A.map t.op P) := by
  simpa only [op_comp, types_comp_apply] using ConcreteCategory.congr_hom (A.map_comp t.op g.op) P

/-- Extend an exact pair match by a further actual test map, in abstract
functor types. The concrete public caller keeps only this opaque tail. -/
private theorem actualContravariantTypeFunctor_pair_match_after_map001
    {C : Type v} [Category.{w} C] (A : Cᵒᵖ ⥤ Type u)
    {T W V U : C} (g : T ⟶ W) (t : W ⟶ V) (i : W ⟶ U)
    (PV : A.obj (.op V)) (PU : A.obj (.op U))
    (hPair : A.map t.op PV = A.map i.op PU) :
    A.map (g ≫ t).op PV = A.map (g ≫ i).op PU := by
  rw [actualContravariantTypeFunctor_map_comp_apply001,
    actualContravariantTypeFunctor_map_comp_apply001]
  exact congrArg (fun P => A.map g.op P) hPair

variable {X B : Scheme.{u}} (F : X ⟶ B) (U V : X.Opens) (n : ℕ) [IsSeparated F]
variable (HU HV : Over B)
variable (etaU : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj HU)
variable (etaV : relativeFiniteFlatHilbertFunctor197 (V.ι ≫ F) n ≅ yoneda.obj HV)

/-- Native315 and the actual transition's whole-ideal law derive equality
of the literal197 pullbacks of the two original universal ambient points. -/
private theorem actualChartUniversalWholeFamily_overlap_point_eq001 :
    (relativeFiniteFlatHilbertFunctor197 F n).map
      (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).op
      (relativeOpenChartUniversalAmbientPoint001 F V n HV etaV) =
    (relativeFiniteFlatHilbertFunctor197 F n).map
      (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).op
      (relativeOpenChartUniversalAmbientPoint001 F U n HU etaU) := by
  have hMatch : relativeOpenChartClassifiedAmbientPoint001 F V n HV etaV
      (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
      (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV) =
      relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
        (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
        (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU) := by
    apply Subtype.ext
    exact (relativeOpenFiniteFlatPointPush_wholeIdeal315 V F n
      (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
      (etaV.inv.app (.op (relativeOpenChartParameterOverlapTest001 F U V n HU etaU))
        (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV))).trans
      (relativeOpenChartParameterOverlapTransition_wholeAmbientIdeal001
        F U V n HU HV etaU etaV)
  exact (relativeOpenChartClassifiedAmbientPoint_eq_pullback001 F V n HV etaV
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
    (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV)).symm.trans
      (hMatch.trans (relativeOpenChartClassifiedAmbientPoint_eq_pullback001 F U n HU etaU
        (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
        (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)))

/-- EVERY original-base scheme test into the actual overlap has the SAME
whole universal family through its two original parameter projections. -/
theorem actualChartUniversalWholeFamily_allTest_overlap_point_eq001
    (T : Over B)
    (g : T ⟶ relativeOpenChartParameterOverlapTest001 F U V n HU etaU) :
    (relativeFiniteFlatHilbertFunctor197 F n).map
      (g ≫ relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).op
      (relativeOpenChartUniversalAmbientPoint001 F V n HV etaV) =
    (relativeFiniteFlatHilbertFunctor197 F n).map
      (g ≫ relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).op
      (relativeOpenChartUniversalAmbientPoint001 F U n HU etaU) := by
  exact actualContravariantTypeFunctor_pair_match_after_map001
    (relativeFiniteFlatHilbertFunctor197 F n) g
    (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV)
    (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)
    (relativeOpenChartUniversalAmbientPoint001 F V n HV etaV)
    (relativeOpenChartUniversalAmbientPoint001 F U n HU etaU)
    (actualChartUniversalWholeFamily_overlap_point_eq001 F U V n HU HV etaU etaV)

/-- Equality of the FULL comapped ideals on the literal197 test ambient.
This is the exact compatibility required by closed-subscheme descent. -/
theorem actualChartUniversalWholeFamily_allTest_overlap_wholeIdeal_eq001
    (T : Over B)
    (g : T ⟶ relativeOpenChartParameterOverlapTest001 F U V n HU etaU) :
    (relativeOpenChartUniversalAmbientPoint001 F V n HV etaV).val.comap
      (relativeHilbertAmbientMap197 F
        (g ≫ relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV)) =
    (relativeOpenChartUniversalAmbientPoint001 F U n HU etaU).val.comap
      (relativeHilbertAmbientMap197 F
        (g ≫ relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)) :=
  congrArg Subtype.val
    (actualChartUniversalWholeFamily_allTest_overlap_point_eq001 F U V n HU HV etaU etaV T g)

/-- For the actual original projective quotient over its original
Noetherian base, BOTH local models/classifiers are constructed internally,
then every actual overlap test has derived whole-ideal matching. -/
theorem originalPositiveHomogeneousCharts_exists_allTestUniversalWholeFamilyOverlap001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (a b : CoordinateRing I) (da db : ℕ)
    (hda : 0 < da) (ha : a ∈ grading I da) (hdb : 0 < db) (hb : b ∈ grading I db)
    (n : ℕ) (hn : 0 < n) :
    ∃ HU HV : Over (Spec (.of R)),
    ∃ etaU : relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj HU,
    ∃ etaV : relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading I) b).ι ≫ toBase I) n ≅ yoneda.obj HV,
    ∀ (T : Over (Spec (.of R)))
      (g : T ⟶ relativeOpenChartParameterOverlapTest001 (toBase I)
        (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU etaU),
      (relativeOpenChartUniversalAmbientPoint001 (toBase I)
        (Proj.basicOpen (grading I) b) n HV etaV).val.comap
        (relativeHilbertAmbientMap197 (toBase I)
          (g ≫ relativeOpenChartParameterOverlapTransition001 (toBase I)
            (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU HV etaU etaV)) =
      (relativeOpenChartUniversalAmbientPoint001 (toBase I)
        (Proj.basicOpen (grading I) a) n HU etaU).val.comap
        (relativeHilbertAmbientMap197 (toBase I)
          (g ≫ relativeOpenChartParameterOverlapInclusion001 (toBase I)
            (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU etaU)) := by
  obtain ⟨HU, hU⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a da hda ha n hn
  obtain ⟨HV, hV⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I b db hdb hb n hn
  let etaU := Classical.choice hU
  let etaV := Classical.choice hV
  refine ⟨HU, HV, etaU, etaV, ?_⟩
  intro T g
  exact actualChartUniversalWholeFamily_allTest_overlap_wholeIdeal_eq001 (toBase I)
    (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU HV etaU etaV T g

end PfaffianDescent
end
