import PfaffianDescent.SchemeModuleUnitHomCokernelFinitePresentation

/-! Actual cokernels between TWO original rank-one modules have native
finite presentations. Source and target frames are used only on common
local charts. No global frame or cokernel/quasicoherence premise.
SOURCE ONLY / UNVERIFIED. Root owns all compiler and acceptance checks. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}

private def rankOneHomCokernelChartPresentation
    (A B : X.Modules) (φ : A ⟶ B) (U : X.Opens)
    (eA : A.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (eB : B.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    {P : ((cokernel φ).over U).Presentation // P.IsFinite} := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  let a0 : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u+1} ≅
      F.obj (SheafOfModules.unit X.ringCatSheaf) :=
    coproductUniqueIso (fun _ : PUnit.{u+1} =>
      SheafOfModules.unit (X.ringCatSheaf.over U)) ≪≫
        (SchemeModuleInternalHom.unitOverIso U).symm
  let a : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u+1} ≅ F.obj A :=
    a0 ≪≫ eA.symm
  let b : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u+1} ≅ F.obj B :=
    a0 ≪≫ eB.symm
  let f := a.hom ≫ F.map φ ≫ b.inv
  let g := b.hom ≫ F.map (cokernel.π φ)
  have H : f ≫ g = 0 := by
    have hmap : F.map φ ≫ F.map (cokernel.π φ) = 0 :=
      (F.map_comp φ (cokernel.π φ)).symm.trans
        ((congrArg (fun k : A ⟶ cokernel φ => F.map k) (cokernel.condition φ)).trans
          (F.map_zero A (cokernel φ)))
    have hbase : f ≫ g = a.hom ≫ (F.map φ ≫ F.map (cokernel.π φ)) := by
      simp only [f, g, Category.assoc, Iso.inv_hom_id_assoc]
    exact hbase.trans ((congrArg (fun k : F.obj A ⟶ F.obj (cokernel φ) => a.hom ≫ k)
      hmap).trans (comp_zero))
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

/-- Common genuine rank-one neighborhoods give a one-generator,
one-relation presentation of the SAME categorical cokernel of φ. -/
theorem schemeModuleRankOneHom_cokernel_isFinitePresentation
    (A B : X.Modules) (hA : schemeModuleLocallyRankOne A)
    (hB : schemeModuleLocallyRankOne B) (φ : A ⟶ B) :
    (cokernel φ).IsFinitePresentation := by
  classical
  obtain ⟨UA, hUA, ⟨eA⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts A hA
  obtain ⟨UB, hUB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts B hB
  let U : X → X.Opens := fun x => UA x ⊓ UB x
  let a (x : X) := SchemeModuleInternalHom.overUnitChartRestrict A
    (homOfLE (show U x ≤ UA x from inf_le_left)) (eA x)
  let b (x : X) := SchemeModuleInternalHom.overUnitChartRestrict B
    (homOfLE (show U x ≤ UB x from inf_le_right)) (eB x)
  have hcover : (Opens.grothendieckTopology X).CoversTop U := by
    apply (Opens.coversTop_iff X U).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hUA x, hUB x⟩
  let q : (cokernel φ).QuasicoherentData :=
    { I := X
      X := U
      coversTop := hcover
      presentation x := (rankOneHomCokernelChartPresentation A B φ (U x) (a x) (b x)).1 }
  have hq : q.IsFinitePresentation :=
    { isFinite_presentation := fun x =>
        (rankOneHomCokernelChartPresentation A B φ (U x) (a x) (b x)).2 }
  have hshrink : q.shrink.IsFinitePresentation :=
    { isFinite_presentation := fun i => hq.isFinite_presentation i.2.choose }
  refine { exists_quasicoherentData := ?_ }
  exact ⟨q.shrink, hshrink⟩

/-- Native quasicoherence follows from the constructed finite presentation
with both ORIGINAL section actions and the ORIGINAL map φ. -/
theorem schemeModuleRankOneHom_cokernel_isQuasicoherent
    (A B : X.Modules) (hA : schemeModuleLocallyRankOne A)
    (hB : schemeModuleLocallyRankOne B) (φ : A ⟶ B) :
    (cokernel φ).IsQuasicoherent := by
  let Q : SheafOfModules.{u} X.ringCatSheaf := cokernel φ
  letI : Q.IsFinitePresentation :=
    schemeModuleRankOneHom_cokernel_isFinitePresentation A B hA hB φ
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData Q
  exact q.isQuasicoherent

end PfaffianDescent
end
