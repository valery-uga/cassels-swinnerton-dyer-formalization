import PfaffianDescent.SchemeModuleNonzeroTopSectionMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! The ACTUAL cokernel of a morphism from the original structure module
to a locally rank-one module has a finite presentation. On each original
rank-one chart, restriction preserves the actual cokernel by its installed
adjunction, and the presentation has one generator and one relation.
This does not assume nonzero sections, support finiteness, or coherence.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual restricted cokernel admits a ONE-generator, ONE-relation
presentation from the actual chart. The colimit witness is derived from
the actual restriction adjunction and original cokernel projection. -/
private def unitHomCokernelChartPresentation
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    {P : ((cokernel φ).over U).Presentation // P.IsFinite} := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  let a : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u+1} ≅
      F.obj (SheafOfModules.unit X.ringCatSheaf) :=
    coproductUniqueIso (fun _ : PUnit.{u+1} =>
      SheafOfModules.unit (X.ringCatSheaf.over U)) ≪≫
        (SchemeModuleInternalHom.unitOverIso U).symm
  let b : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u+1} ≅ F.obj M :=
    a ≪≫ e.symm
  let f := a.hom ≫ F.map φ ≫ b.inv
  let g := b.hom ≫ F.map (cokernel.π φ)
  have H : f ≫ g = 0 := by
    simp only [f, g, Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp,
      cokernel.condition, Functor.map_zero, comp_zero]
  let hc := isColimitOfHasCokernelOfPreservesColimit F φ
  have hfg : IsColimit (CokernelCofork.ofπ g H) := by
    exact CokernelCofork.isColimitOfIsColimitOfIff
      (isCokernelEpiComp hc a.hom rfl) f b (by
        intro Z k
        simp only [f, Category.assoc, Iso.inv_hom_id_assoc])
  let P := SheafOfModules.presentationOfIsCokernelFree f g H hfg
  refine ⟨P, ?_⟩
  refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
  · exact { finite := inferInstanceAs (Finite PUnit.{u+1}) }
  · exact { finite := inferInstanceAs (Finite PUnit.{u+1}) }

/-- Actual local rank-one geometry internally supplies a finite local
presentation of the SAME categorical cokernel of the SAME original map.
No cokernel-preservation, quasicoherence, or section-comparison premise is
required. Empty schemes are included by the point-indexed cover. -/
theorem schemeModuleUnitHom_cokernel_isFinitePresentation
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    (cokernel φ).IsFinitePresentation := by
  classical
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  have hcover : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  let q : (cokernel φ).QuasicoherentData :=
    { I := X
      X := B
      coversTop := hcover
      presentation x := (unitHomCokernelChartPresentation M φ (B x) (eB x)).1 }
  have hq : q.IsFinitePresentation :=
    { isFinite_presentation := fun x =>
        (unitHomCokernelChartPresentation M φ (B x) (eB x)).2 }
  have hshrink : q.shrink.IsFinitePresentation :=
    { isFinite_presentation := fun i => hq.isFinite_presentation i.2.choose }
  refine { exists_quasicoherentData := ?_ }
  exact ⟨q.shrink, hshrink⟩

/-- Quasicoherence is obtained from the constructed finite presentation,
with the original rings and original morphism unchanged. -/
theorem schemeModuleUnitHom_cokernel_isQuasicoherent
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    (cokernel φ).IsQuasicoherent := by
  letI := schemeModuleUnitHom_cokernel_isFinitePresentation M hM φ
  infer_instance

/-- In particular, the cokernel of the literal unit map determined by an
ACTUAL top-open section has finite presentation and is quasicoherent. The
conclusion holds even for the zero section; nonzero is used separately to
derive Mono and the zero generic stalk. -/
theorem schemeModuleTopSectionHom_cokernel_isFinitePresentation_and_isQuasicoherent
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) :
    (cokernel (schemeModuleTopSectionHom M s)).IsFinitePresentation ∧
      (cokernel (schemeModuleTopSectionHom M s)).IsQuasicoherent :=
  ⟨schemeModuleUnitHom_cokernel_isFinitePresentation M hM _,
    schemeModuleUnitHom_cokernel_isQuasicoherent M hM _⟩

end PfaffianDescent
