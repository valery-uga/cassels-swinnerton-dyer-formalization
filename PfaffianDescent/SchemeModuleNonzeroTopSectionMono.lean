import PfaffianDescent.SchemeModuleFixedFrameUnitStalkFunctionField
import PfaffianDescent.SchemeModuleFixedFrameStalkInjectiveOfLocallyRankOne
import PfaffianDescent.SchemeModuleSectionOnOpen
import PfaffianDescent.SchemeModuleStalkMono
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! An actual nonzero top-open section of an integral scheme's locally
rank-one module defines an actual monomorphism from the original unit.
The stalk map follows multiplication by its SAME original field value.
The literal categorical cokernel sequence is consequently short exact.
This implication does not assert existence of a nonzero section, finite
support, local length finiteness, or a weighted cycle degree. SOURCE ONLY. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original unit-module adjunction applied to the compatible family
of restrictions of the SAME top-open section. No rational frame enters
this definition. -/
def schemeModuleTopSectionHom (M : X.Modules) (s : M.val.obj (op ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm ((schemeModuleSectionsEquivTop M).symm s)

/-- The actual section morphism takes the native unit to the original
section, rather than to a compared or renamed section. -/
theorem schemeModuleTopSectionHom_value (M : X.Modules) (s : M.val.obj (op ⊤)) :
    (schemeModuleTopSectionHom M s).val.app (op ⊤) (1 : Γ(X, ⊤)) = s := by
  have h := congrArg (schemeModuleSectionsEquivTop M)
    (M.unitHomEquiv.apply_symm_apply ((schemeModuleSectionsEquivTop M).symm s))
  change (schemeModuleTopSectionHom M s).val.app (op ⊤) (1 : Γ(X, ⊤)) =
    schemeModuleSectionsEquivTop M ((schemeModuleSectionsEquivTop M).symm s) at h
  exact h.trans ((schemeModuleSectionsEquivTop M).apply_symm_apply s)

variable {K : Type u} [Field K] [IsIntegral X]

private theorem unitHom_stalk_one
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (x : X) :
    let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    letI := schemeModuleStalkModule O x
    letI := schemeModuleStalkModule M x
    schemeModuleStalkLinearMap φ x ((schemeModuleUnitStalkIso X x).inv.hom
        (1 : X.presheaf.stalk x)) =
      M.presheaf.germ ⊤ x trivial (φ.val.app (op ⊤) (1 : Γ(X, ⊤))) := by
  dsimp only
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI := schemeModuleStalkModule O x
  letI := schemeModuleStalkModule M x
  let E := schemeModuleUnitStalkIso X x
  have hu : E.inv.hom (1 : X.presheaf.stalk x) =
      O.presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤)) :=
    (congrArg E.inv.hom (X.presheaf.germ ⊤ x trivial).hom.map_one).symm.trans
      (presheafOfModules_unitStalkAddEquiv_germ X.presheaf x ⊤ trivial (1 : Γ(X, ⊤)))
  have hg : schemeModuleStalkLinearMap φ x
      (O.presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤))) =
      M.presheaf.germ ⊤ x trivial (φ.val.app (op ⊤) (1 : Γ(X, ⊤))) := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((Scheme.Modules.toPresheaf X).map φ)
      (O.presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤))) = _
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
      ((Scheme.Modules.toPresheaf X).map φ) (1 : Γ(X, ⊤))
  exact (congrArg (schemeModuleStalkLinearMap φ x) hu).trans hg

/-- At EVERY original point, the actual section morphism followed by the
actual fixed-frame stalk map is multiplication by the SAME original global
field value. The unit-stalk factor uses the SAME native map; this is proved
from original germ laws and local-ring linearity, not assumed compatibility. -/
theorem schemeModuleUnitHom_stalkField_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) (hgC : genericPoint X ∈ C)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (x : X) :
    letI : Nonempty C := ⟨⟨genericPoint X, hgC⟩⟩
    let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    letI := schemeModuleStalkModule O x
    letI := schemeModuleStalkModule M x
    ∀ a : O.presheaf.stalk x,
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x
          (schemeModuleStalkLinearMap φ x a) =
        @HMul.hMul X.functionField X.functionField X.functionField inferInstance
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x a)
          (schemeModuleTopSectionsToFunctionFieldLinearMap pi M C hgC e
            (φ.val.app (op ⊤) (1 : Γ(X, ⊤)))) := by
  dsimp only
  letI : Nonempty C := ⟨⟨genericPoint X, hgC⟩⟩
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI := schemeModuleStalkModule O x
  letI := schemeModuleStalkModule M x
  let E := (schemeModuleUnitStalkIso X x).toLinearEquiv
  let L := (schemeModuleStalkLinearMap φ x).comp E.symm.toLinearMap
  let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x
  let ψO := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x
  let κ := algebraMap (X.presheaf.stalk x) X.functionField
  let s : M.val.obj (op ⊤) := φ.val.app (op ⊤) (1 : Γ(X, ⊤))
  let f : X.functionField := schemeModuleTopSectionsToFunctionFieldLinearMap pi M C hgC e s
  have hL1 : L (1 : X.presheaf.stalk x) = M.presheaf.germ ⊤ x trivial s :=
    unitHom_stalk_one M φ x
  have hψ1 : ψ (L (1 : X.presheaf.stalk x)) = f :=
    (congrArg ψ hL1).trans
      (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_global_germ pi M C e x s)
  intro a
  let r := E a
  have hLa : schemeModuleStalkLinearMap φ x a = r • L (1 : X.presheaf.stalk x) := by
    calc
      schemeModuleStalkLinearMap φ x a = L r :=
        (congrArg (schemeModuleStalkLinearMap φ x) (E.symm_apply_apply a)).symm
      _ = L (r • (1 : X.presheaf.stalk x)) :=
        congrArg L (show r • (1 : X.presheaf.stalk x) = r from mul_one r).symm
      _ = r • L (1 : X.presheaf.stalk x) := L.map_smul r _
  have hκ : ψO a = κ r :=
    schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_apply pi C x a
  change ψ (schemeModuleStalkLinearMap φ x a) = ψO a * f
  exact (congrArg ψ hLa).trans
    ((ψ.map_smul r (L (1 : X.presheaf.stalk x))).trans
      ((congrArg (fun t : X.functionField => κ r * t) hψ1).trans
        (congrArg (fun c : X.functionField => c * f) hκ).symm))

/-- A given ACTUAL nonzero top-open section produces a genuine monic
original unit map and its genuine cokernel short exact sequence. Rank-one
geometry detects the original nonzero section in the function field;
native unit-stalk injectivity detects the actual kernel at every point. -/
theorem schemeModuleTopSectionHom_mono_and_cokernelSequence_shortExact
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (C : X.Opens) (hgC : genericPoint X ∈ C)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    Mono (schemeModuleTopSectionHom M s) ∧
      (ShortComplex.cokernelSequence (schemeModuleTopSectionHom M s)).ShortExact := by
  letI : Nonempty C := ⟨⟨genericPoint X, hgC⟩⟩
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let φ := schemeModuleTopSectionHom M s
  let Φ := schemeModuleTopSectionsToFunctionFieldLinearMap pi M C hgC e
  have hf : (Φ s : X.functionField) ≠ 0 := by
    intro hf
    exact hs (schemeModuleTopSectionsToFunctionFieldLinearMap_injective pi M hM C hgC e
      (hf.trans Φ.map_zero.symm))
  have hmono : Mono φ := by
    apply schemeModule_mono_of_stalk_mono
    intro x
    letI := schemeModuleStalkModule O x
    letI := schemeModuleStalkModule M x
    let ψO := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x
    let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x
    apply ConcreteCategory.mono_of_injective ((schemeModuleStalkFunctor X x).map φ)
    intro a b hab
    have hab' : schemeModuleStalkLinearMap φ x a = schemeModuleStalkLinearMap φ x b := hab
    have hval (a : O.presheaf.stalk x) : ψ (schemeModuleStalkLinearMap φ x a) =
        @HMul.hMul X.functionField X.functionField X.functionField inferInstance (ψO a) (Φ s) :=
      (schemeModuleUnitHom_stalkField_apply pi M C hgC e φ x a).trans
        (congrArg (fun t : M.val.obj (op ⊤) =>
          @HMul.hMul X.functionField X.functionField X.functionField inferInstance (ψO a) (Φ t))
          (schemeModuleTopSectionHom_value M s))
    apply (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_injective_and_range pi C x).1
    exact mul_right_cancel₀ hf ((hval a).symm.trans ((congrArg ψ hab').trans (hval b)))
  letI : Mono φ := hmono
  refine ⟨hmono, ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact φ) ?_ (by infer_instance)⟩
  change Mono φ
  exact hmono

end PfaffianDescent
