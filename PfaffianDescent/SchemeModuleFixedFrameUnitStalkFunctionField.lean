import PfaffianDescent.SchemeModuleFixedFrameFunctionFieldShrinking

/-! The actual unit base-word stalk field map is the native algebraMap.
Original Iso.refl charts, actual shrinking and the existing unit-stalk
comparison prove the identity. No replacement action/frame/image input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restrict_unit_refl {B C : X.Opens} (f : C ⟶ B) :
    SchemeModuleInternalHom.overUnitChartRestrict
        (SheafOfModules.unit X.ringCatSheaf) f (Iso.refl _) = Iso.refl _ := by
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let theta := SheafOfModules.overFunctorMap X.ringCatSheaf f
  apply Iso.ext
  change ((theta.app O).inv ≫ (SheafOfModules.overMap X.ringCatSheaf f).map
      (𝟙 (O.over B))) ≫ (theta.app O).hom = 𝟙 (O.over C)
  rw [(SheafOfModules.overMap X.ringCatSheaf f).map_id]
  exact (congrArg (fun k => k ≫ (theta.app O).hom)
    (Category.comp_id (theta.app O).inv)).trans (theta.app O).inv_hom_id

variable {K : Type u} [Field K] [IsIntegral X]

private theorem generic_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

private theorem unitOpen_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (C : X.Opens) [Nonempty C]
    (U : X.Opens) [Nonempty U] (r : Γ(X, U)) :
    (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi
        (SheafOfModules.unit X.ringCatSheaf) C (Iso.refl _) U r : X.functionField) =
      X.germToFunctionField U r := by
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let W : X.Opens := U ⊓ C
  letI : Nonempty W := ⟨⟨genericPoint X, generic_mem U, generic_mem C⟩⟩
  let f : W ⟶ U := homOfLE inf_le_left
  let g : W ⟶ C := homOfLE inf_le_right
  have hc : (((Iso.refl (O.over C)).hom.val.app (op (Over.mk g)))
      (O.val.map f.op r) : Γ(X, W)) = X.presheaf.map f.op r := rfl
  exact (schemeModuleFixedFrameOpenToFunctionFieldLinearMap_apply pi O C (Iso.refl _) U r).trans
    ((congrArg (X.germToFunctionField W) hc).trans
      (X.presheaf.germ_res_apply f (genericPoint X) (generic_mem W) r))

/-- The unit base-word map composed with the SAME canonical unit-stalk
Iso inverse is the native stalk-to-field algebraMap as an actual linear
map. Original unit charts/shrinking/germs derive this identity internally. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_comp_inv
    (pi : X ⟶ Spec (CommRingCat.of K)) (C : X.Opens) [Nonempty C] (x : X) :
    let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    letI := schemeModuleStalkModule O x
    (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x).comp
        (schemeModuleUnitStalkIso X x).inv.hom =
      Algebra.linearMap (X.presheaf.stalk x) X.functionField := by
  dsimp only
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI := schemeModuleStalkModule O x
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  let f : C ⟶ (⊤ : X.Opens) := homOfLE le_top
  let ψC := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x
  let ψTop := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O ⊤ (Iso.refl _) x
  have hψ : ψC = ψTop :=
    (congrArg (fun e => schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C e x)
      (restrict_unit_refl f)).symm.trans
        (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_shrink pi O ⊤ C f (Iso.refl _) x)
  apply LinearMap.ext
  intro r
  change ψC ((schemeModuleUnitStalkIso X x).inv.hom r) =
    algebraMap (X.presheaf.stalk x) X.functionField r
  obtain ⟨U, hxU, rU, rfl⟩ := X.presheaf.exists_germ_eq r
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hg : (schemeModuleUnitStalkIso X x).inv.hom (X.presheaf.germ U x hxU rU) =
      O.presheaf.germ U x hxU rU :=
    presheafOfModules_unitStalkAddEquiv_germ X.presheaf x U hxU rU
  exact (DFunLike.congr_fun hψ _).trans
    ((congrArg ψTop hg).trans
      ((schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi O ⊤ (Iso.refl _) x U hxU rU).trans
        ((unitOpen_apply pi ⊤ U rU).trans
          (Scheme.algebraMap_germ_eq_germToFunctionField X hxU rU).symm)))

/-- Actual value on EVERY unit-module stalk element, using the ORIGINAL
unit-stalk Iso forward map; no scalar action is transported or replaced. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (C : X.Opens) [Nonempty C] (x : X) :
    let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    letI := schemeModuleStalkModule O x
    ∀ a : O.presheaf.stalk x,
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x a =
        algebraMap (X.presheaf.stalk x) X.functionField ((schemeModuleUnitStalkIso X x).hom.hom a) := by
  dsimp only
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI := schemeModuleStalkModule O x
  let E := (schemeModuleUnitStalkIso X x).toLinearEquiv
  let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x
  intro a
  have he : (schemeModuleUnitStalkIso X x).inv.hom ((schemeModuleUnitStalkIso X x).hom.hom a) = a :=
    E.symm_apply_apply a
  exact (congrArg ψ he).symm.trans
    (DFunLike.congr_fun (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_comp_inv pi C x)
      ((schemeModuleUnitStalkIso X x).hom.hom a))

/-- The actual unit base-word stalk map is injective and has the FULL
native local-ring field image, internally from the SAME native Iso and
integral field map. Neither assertion is a supplied word-base condition. -/
theorem schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_injective_and_range
    (pi : X ⟶ Spec (CommRingCat.of K)) (C : X.Opens) [Nonempty C] (x : X) :
    let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    letI := schemeModuleStalkModule O x
    let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x
    Function.Injective ψ ∧ Set.range ψ =
      Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  dsimp only
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI := schemeModuleStalkModule O x
  let E := (schemeModuleUnitStalkIso X x).toLinearEquiv
  let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x
  let κ := algebraMap (X.presheaf.stalk x) X.functionField
  constructor
  · intro a b hab
    apply E.injective
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_apply pi C x a).symm.trans
      (hab.trans (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_apply pi C x b))
  · apply Set.Subset.antisymm
    · rintro z ⟨a, ha⟩
      exact ⟨E a, (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_apply pi C x a).symm.trans ha⟩
    · rintro z ⟨r, hr⟩
      exact ⟨E.symm r,
        (DFunLike.congr_fun (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_comp_inv pi C x) r).trans hr⟩

end PfaffianDescent
