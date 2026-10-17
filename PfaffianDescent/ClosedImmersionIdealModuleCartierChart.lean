import PfaffianDescent.ClosedImmersionIdealModuleLocallyFree

/-! The local ideal-module inclusion is multiplication by its defining equation. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- Under the section-induced trivialization, the actual closed-immersion
ideal module includes into the structure sheaf by multiplication by the
restricted image of its defining section. -/
theorem closedImmersionModule_sectionOnOpenHom_toUnit_apply
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    (U : X.Opens)
    (t : (IdealSheafDataModule.closedImmersionModule f).val.presheaf.obj
      (Opposite.op U)) (V : (U : Scheme.{u}).Opens)
    (a : Γ((U : Scheme.{u}), V)) :
    let hVU : U.ι ''ᵁ V ≤ U := by
      simpa only [U.ι_image_top] using
        (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))
    let M : X.Modules := IdealSheafDataModule.closedImmersionModule f
    ((closedImmersionModuleRestrictToUnit f U).val.app (Opposite.op V))
      (((schemeModuleSectionOnOpenHom M U t).val.app (Opposite.op V)) a) =
      a * (U.ι.appIso V).hom
        (X.presheaf.map (homOfLE hVU).op
          (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
            (Opposite.op U)) t)) := by
  dsimp only
  let M : X.Modules := IdealSheafDataModule.closedImmersionModule f
  let φ := schemeModuleSectionOnOpenHom M U t
  let ψ := closedImmersionModuleRestrictToUnit f U
  let hVU : U.ι ''ᵁ V ≤ U := by
    simpa only [U.ι_image_top] using
      (Scheme.Hom.image_mono U.ι (show V ≤ ⊤ from le_top))
  letI : Module (Γ((U : Scheme.{u}), V))
      ((M.restrict U.ι).val.obj (Opposite.op V) : ModuleCat _) :=
    ((M.restrict U.ι).val.obj (Opposite.op V)).isModule
  letI : Module (Γ((U : Scheme.{u}), V))
      ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.obj
        (Opposite.op V) : ModuleCat _) :=
    ((SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).val.obj
      (Opposite.op V)).isModule
  have hφ := schemeModuleUnitHom_apply_eq_smul_one (M.restrict U.ι) φ V a
  have hvalue : ψ.val.app (Opposite.op V)
      (φ.val.app (Opposite.op V) (1 : Γ((U : Scheme.{u}), V))) =
      (U.ι.appIso V).hom
        (X.presheaf.map (homOfLE hVU).op
          (((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
            (Opposite.op U)) t)) := by
    have h₁ := closedImmersionModuleRestrictToUnit_apply f U V
      (φ.val.app (Opposite.op V) (1 : Γ((U : Scheme.{u}), V)))
    have h₂ := closedImmersionModule_sectionOnOpenHom_restrict_image f U t V
    exact h₁.trans (congrArg (fun y => (U.ι.appIso V).hom y) h₂)
  calc
    ψ.val.app (Opposite.op V) (φ.val.app (Opposite.op V) a) =
        ψ.val.app (Opposite.op V)
          (a • φ.val.app (Opposite.op V) (1 : Γ((U : Scheme.{u}), V))) := by
            rw [hφ]
    _ = a • ψ.val.app (Opposite.op V)
          (φ.val.app (Opposite.op V) (1 : Γ((U : Scheme.{u}), V))) := by
            exact (ψ.val.app (Opposite.op V)).hom.map_smul a _
    _ = _ := by rw [hvalue]; rfl

/-- On a regular-principal chart, the actual ideal-module inclusion is
multiplication by the chosen regular equation after trivialization. -/
theorem RegularPrincipalImmersion.chartIdealModuleHom_toUnit_apply
    {X Z : Scheme.{u}} {f : Z ⟶ X} [IsClosedImmersion f]
    (H : RegularPrincipalImmersion f) (j : H.Index)
    [IsOpenImmersion (H.target j)] :
    let W : (Spec (H.A j)).affineOpens :=
      ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
    let U : X.affineOpens :=
      ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
    let z := Classical.choose (H.exists_closedImmersionModule_chart_generator j)
    ∀ (V : (U.1 : Scheme.{u}).Opens) (a : Γ((U.1 : Scheme.{u}), V)),
      let hVU : U.1.ι ''ᵁ V ≤ U.1 := by
        simpa only [U.1.ι_image_top] using
          (Scheme.Hom.image_mono U.1.ι (show V ≤ ⊤ from le_top))
      ((closedImmersionModuleRestrictToUnit f U.1).val.app (Opposite.op V))
        (((H.chartIdealModuleHom j).val.app (Opposite.op V)) a) =
        a * (U.1.ι.appIso V).hom
          (X.presheaf.map (homOfLE hVU).op z) := by
  dsimp only
  let W : (Spec (H.A j)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
  let U : X.affineOpens :=
    ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  let data := H.exists_closedImmersionModule_chart_generator j
  let z := Classical.choose data
  let t := Classical.choose (Classical.choose_spec data)
  have ht : ((IdealSheafDataModule.closedImmersionModuleToUnit f).val.app
      (Opposite.op U.1)) t = z :=
    (Classical.choose_spec (Classical.choose_spec data)).2.1
  intro V a
  have h := closedImmersionModule_sectionOnOpenHom_toUnit_apply f U.1 t V a
  rw [ht] at h
  exact h

end PfaffianDescent
