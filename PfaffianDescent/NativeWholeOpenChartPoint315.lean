import PfaffianDescent.NativeFiniteFamilyOpenLocus314
import PfaffianDescent.RelativeClosedAmbientTestMap313

/-! SOURCE ONLY315. ACTUAL entire original finite family on the canonical
good base is assembled into the original relative open chart. Its closed
immersion and whole ambient recovery are derived, never supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
variable (P : FiniteFlatHilbertPoint195 F n) (U : X.Opens)

include P U in
def wholeOpenGoodAmbient315 : Scheme.{u} :=
  pullback (finiteFamilyWholeOpenLocus314 F n P U).ι F

include P U in
def wholeOpenGoodChartAmbient315 : Scheme.{u} :=
  pullback (finiteFamilyWholeOpenLocus314 F n P U).ι (U.ι ≫ F)

include P U in
def wholeOpenGoodChartToAmbient315 :
    wholeOpenGoodChartAmbient315 F n P U ⟶ wholeOpenGoodAmbient315 F n P U :=
  relativeClosedAmbientTestMap313 U.ι F (Over.mk (finiteFamilyWholeOpenLocus314 F n P U).ι)

lemma wholeOpenGoodChartToAmbient_isOpenImmersion315 :
    IsOpenImmersion (wholeOpenGoodChartToAmbient315 F n P U) :=
  MorphismProperty.of_isPullback
    (relativeClosedAmbientTestMap_isPullback313 U.ι F
      (Over.mk (finiteFamilyWholeOpenLocus314 F n P U).ι)).flip
    (inferInstance : IsOpenImmersion U.ι)

include P U in
/-- The SAME restricted original source maps to the literal original ambient fiber product. -/
def wholeOpenGoodSourceToAmbient315 :
    (finiteFamilyWholeOpenSource314 F n P U).toScheme ⟶ wholeOpenGoodAmbient315 F n P U :=
  pullback.lift (finiteFamilyWholeOpenProjection314 F n P U)
    ((finiteFamilyWholeOpenSource314 F n P U).ι ≫ P.val.subschemeι)
    ((morphismRestrict_ι (P.val.subschemeι ≫ F)
      (finiteFamilyWholeOpenLocus314 F n P U)).trans (Category.assoc _ _ _).symm)

lemma wholeOpenGoodSourceToAmbient_fst315 :
    wholeOpenGoodSourceToAmbient315 F n P U ≫
      pullback.fst (finiteFamilyWholeOpenLocus314 F n P U).ι F =
        finiteFamilyWholeOpenProjection314 F n P U := pullback.lift_fst _ _ _

lemma wholeOpenGoodSourceToAmbient_snd315 :
    wholeOpenGoodSourceToAmbient315 F n P U ≫
      pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι F =
        (finiteFamilyWholeOpenSource314 F n P U).ι ≫ P.val.subschemeι :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma wholeOpenGoodSourceToAmbient_isPullback315 :
    IsPullback (finiteFamilyWholeOpenSource314 F n P U).ι
      (wholeOpenGoodSourceToAmbient315 F n P U) P.val.subschemeι
      (pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι F) := by
  have Houter : IsPullback (finiteFamilyWholeOpenSource314 F n P U).ι
      (wholeOpenGoodSourceToAmbient315 F n P U ≫
        pullback.fst (finiteFamilyWholeOpenLocus314 F n P U).ι F)
      (P.val.subschemeι ≫ F) (finiteFamilyWholeOpenLocus314 F n P U).ι := by
    rw [wholeOpenGoodSourceToAmbient_fst315]
    exact finiteFamilyWholeOpenProjection_isPullback314 F n P U
  exact Houter.of_bot (wholeOpenGoodSourceToAmbient_snd315 F n P U).symm
    (IsPullback.of_hasPullback (finiteFamilyWholeOpenLocus314 F n P U).ι F).flip

lemma wholeOpenGoodSourceToAmbient_isClosedImmersion315 :
    IsClosedImmersion (wholeOpenGoodSourceToAmbient315 F n P U) :=
  MorphismProperty.of_isPullback (wholeOpenGoodSourceToAmbient_isPullback315 F n P U)
    (inferInstance : IsClosedImmersion P.val.subschemeι)

include P U in
/-- Actual map into U×[B]goodBase, from the internally derived entire-family lift314. -/
def wholeOpenGoodSourceToChart315 :
    (finiteFamilyWholeOpenSource314 F n P U).toScheme ⟶ wholeOpenGoodChartAmbient315 F n P U :=
  pullback.lift (finiteFamilyWholeOpenProjection314 F n P U)
    (finiteFamilyWholeOpenChartLift314 F n P U)
    (finiteFamilyWholeOpenChartLift_toBase314 F n P U).symm

lemma wholeOpenGoodSourceToChart_fst315 :
    wholeOpenGoodSourceToChart315 F n P U ≫
      pullback.fst (finiteFamilyWholeOpenLocus314 F n P U).ι (U.ι ≫ F) =
        finiteFamilyWholeOpenProjection314 F n P U := pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma wholeOpenGoodSourceToChart_toAmbient315 :
    wholeOpenGoodSourceToChart315 F n P U ≫ wholeOpenGoodChartToAmbient315 F n P U =
      wholeOpenGoodSourceToAmbient315 F n P U := by
  have hf : wholeOpenGoodChartToAmbient315 F n P U ≫
      pullback.fst (finiteFamilyWholeOpenLocus314 F n P U).ι F =
      pullback.fst (finiteFamilyWholeOpenLocus314 F n P U).ι (U.ι ≫ F) :=
    relativeClosedAmbientTestMap_toTest313 U.ι F
      (Over.mk (finiteFamilyWholeOpenLocus314 F n P U).ι)
  have hs : wholeOpenGoodChartToAmbient315 F n P U ≫
      pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι F =
      pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι (U.ι ≫ F) ≫ U.ι :=
    relativeClosedAmbientTestMap_toOriginal313 U.ι F
      (Over.mk (finiteFamilyWholeOpenLocus314 F n P U).ι)
  have ha : wholeOpenGoodSourceToChart315 F n P U ≫
      pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι (U.ι ≫ F) =
      finiteFamilyWholeOpenChartLift314 F n P U := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => wholeOpenGoodSourceToChart315 F n P U ≫ k) hf).trans
        ((wholeOpenGoodSourceToChart_fst315 F n P U).trans
          (wholeOpenGoodSourceToAmbient_fst315 F n P U).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => wholeOpenGoodSourceToChart315 F n P U ≫ k) hs).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ U.ι) ha).trans
            ((finiteFamilyWholeOpenChartLift_comp314 F n P U).trans
              (wholeOpenGoodSourceToAmbient_snd315 F n P U).symm))))

lemma wholeOpenGoodSourceToChart_isClosedImmersion315 :
    IsClosedImmersion (wholeOpenGoodSourceToChart315 F n P U) := by
  letI := wholeOpenGoodChartToAmbient_isOpenImmersion315 F n P U
  letI : IsClosedImmersion (wholeOpenGoodSourceToChart315 F n P U ≫
      wholeOpenGoodChartToAmbient315 F n P U) :=
    (wholeOpenGoodSourceToChart_toAmbient315 F n P U).symm ▸
      wholeOpenGoodSourceToAmbient_isClosedImmersion315 F n P U
  exact IsClosedImmersion.of_comp (wholeOpenGoodSourceToChart315 F n P U)
    (wholeOpenGoodChartToAmbient315 F n P U)

include P U in
/-- Genuine literal195 point in SAME relative chart, all properties derived internally. -/
def wholeOpenGoodChartPoint315 :
    FiniteFlatHilbertPoint195
      (pullback.fst (finiteFamilyWholeOpenLocus314 F n P U).ι (U.ι ≫ F)) n := by
  let a := wholeOpenGoodSourceToChart315 F n P U
  let f := pullback.fst (finiteFamilyWholeOpenLocus314 F n P U).ι (U.ι ≫ F)
  have ha : a ≫ f = finiteFamilyWholeOpenProjection314 F n P U :=
    wholeOpenGoodSourceToChart_fst315 F n P U
  have hclosed : IsClosedImmersion a := wholeOpenGoodSourceToChart_isClosedImmersion315 F n P U
  have hfinite : IsFinite (a ≫ f) := ha.symm ▸ finiteFamilyWholeOpenProjection_finite314 F n P U
  have hflat : Flat (a ≫ f) := ha.symm ▸ finiteFamilyWholeOpenProjection_flat314 F n P U
  exact @closedImmersionHilbertPoint195 _ _ _ f a hclosed hfinite hflat n
    (fun b => ha.symm ▸ finiteFamilyWholeOpenProjection_finrank314 F n P U b)

lemma wholeOpenGoodChartPoint_wholeIdeal315 :
    (wholeOpenGoodChartPoint315 F n P U).val = (wholeOpenGoodSourceToChart315 F n P U).ker := rfl

lemma wholeOpenGoodChartPoint_originalAmbientIdeal315 :
    (wholeOpenGoodChartPoint315 F n P U).val.map (wholeOpenGoodChartToAmbient315 F n P U) =
      P.val.comap (pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι F) := by
  have hk : (wholeOpenGoodSourceToAmbient315 F n P U).ker =
      P.val.comap (pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι F) :=
    (wholeIdeal_comap_eq_of_isPullback195 (finiteFamilyWholeOpenSource314 F n P U).ι
      (wholeOpenGoodSourceToAmbient315 F n P U) P.val.subschemeι
      (pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι F)
      (wholeOpenGoodSourceToAmbient_isPullback315 F n P U)).symm.trans
        (congrArg (fun I => I.comap
          (pullback.snd (finiteFamilyWholeOpenLocus314 F n P U).ι F)) P.val.ker_subschemeι)
  exact (congrArg (fun I => I.map (wholeOpenGoodChartToAmbient315 F n P U))
    (wholeOpenGoodChartPoint_wholeIdeal315 F n P U)).trans
      ((Scheme.IdealSheafData.map_ker _ _).trans
        ((congrArg (fun a => a.ker) (wholeOpenGoodSourceToChart_toAmbient315 F n P U)).trans hk))

end PfaffianDescent
end
