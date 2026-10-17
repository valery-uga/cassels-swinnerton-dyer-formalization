import PfaffianDescent.CorayPushforwardCechCoefficientNaturality
import PfaffianDescent.SectionRepresenterCanonicalRestriction
import PfaffianDescent.SchemeCoverIntrinsicCohomology

/-! The actual original cover augmentation and actual pushforward-unit map
commute with original preimage section transport. SOURCE ONLY / UNVERIFIED.
No desired Ext-map compatibility is an input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X Y : Scheme.{u}} {ι : Type u}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem normalizedCechAugmentation_coordinate (U : ι → X.Opens)
    (M : X.Modules) (q : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (a : Fin 1 → ι) :
    sectionRepresenterCechHomEquivPi X.ringCatSheaf U M 0
      (sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
        (schemeCoverCechTargetIsoUnit U).hom ≫ q) a =
      q.val.app (op (∏ᶜ fun b : Fin 1 => U (a b)))
        (1 : Γ(X, ∏ᶜ fun b : Fin 1 => U (a b))) := by
  let V : X.Opens := ∏ᶜ fun b : Fin 1 => U (a b)
  let j : V ⟶ (⊤ : X.Opens) := isTerminalTop.from V
  have hc :
      Sigma.ι (fun c : Fin 1 → ι =>
        sectionRepresenter X.ringCatSheaf (∏ᶜ fun b : Fin 1 => U (c b))) a ≫
        (sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
          (schemeCoverCechTargetIsoUnit U).hom ≫ q) =
      (sectionRepresenterFunctor X.ringCatSheaf).map j ≫
        (sectionRepresenterTopIsoUnit X).hom ≫ q := by
    have h := sectionRepresenterCechAugmentation_component X.ringCatSheaf U
      (⊤ : X.Opens) isTerminalTop a
    have ht := congrArg (fun k :
        (show X.Modules from sectionRepresenter X.ringCatSheaf V) ⟶
          (show X.Modules from sectionRepresenter X.ringCatSheaf (⊤ : X.Opens)) =>
        k ≫ (sectionRepresenterTopIsoUnit X).hom ≫ q) h
    simpa only [schemeCoverCechTargetIsoUnit, Iso.trans_hom, Category.assoc] using ht
  change sectionRepresenterHomEquiv X.ringCatSheaf V M
    (Sigma.ι (fun c : Fin 1 → ι =>
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun b : Fin 1 => U (c b))) a ≫
        (sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
          (schemeCoverCechTargetIsoUnit U).hom ≫ q)) = _
  rw [hc, sectionRepresenterHomEquiv_precomp, sectionRepresenterHomEquiv_postcomp,
    sectionRepresenterTopIsoUnit_hom_coordinate]
  have hn := ConcreteCategory.congr_hom (q.val.naturality j.op) (1 : Γ(X, ⊤))
  change M.val.map j.op (q.val.app (op ⊤) (1 : Γ(X, ⊤))) =
    q.val.app (op V) (1 : Γ(X, V))
  exact hn.symm.trans (congrArg (fun s => q.val.app (op V) s)
    ((X.ringCatSheaf.obj.map j.op).hom.map_one))

private theorem openEq_unit_one {V W : Y.Opens} (h : V = W) :
    schemeModule_openEqSectionsAddEquiv (SheafOfModules.unit Y.ringCatSheaf) h
      (1 : Γ(Y, V)) = (1 : Γ(Y, W)) := by
  subst W
  rfl

private theorem openEq_postcomp (M N : Y.Modules)
    {V W : Y.Opens} (h : V = W) (g : M ⟶ N) (s : M.val.obj (op V)) :
    schemeModule_openEqSectionsAddEquiv N h (g.val.app (op V) s) =
      g.val.app (op W) (schemeModule_openEqSectionsAddEquiv M h s) := by
  subst W
  rfl

/-- The SAME degree-zero preimage cochain transport sends the actual
normalized augmentation of the actual pushforward-unit image of q to the
actual normalized augmentation of q. Coproduct coordinates and the
original ring-map value at one derive the square internally. -/
theorem schemeModulePushforwardCechHomAddEquiv_normalizedAugmentation
    (f : Y ⟶ X) (M : Y.Modules) (U : ι → X.Opens)
    (q : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    schemeModulePushforwardCechHomAddEquiv f M U 0
      (sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
        (schemeCoverCechTargetIsoUnit U).hom ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map q) =
      sectionRepresenterCechAugmentation Y.ringCatSheaf
        (fun a => f ⁻¹ᵁ U a) ⊤ isTerminalTop ≫
        (schemeCoverCechTargetIsoUnit (fun a => f ⁻¹ᵁ U a)).hom ≫ q := by
  apply (sectionRepresenterCechHomAddEquivPi Y.ringCatSheaf
    (fun a => f ⁻¹ᵁ U a) M 0).injective
  funext a
  erw [schemeModulePushforwardCechHomAddEquiv_apply,
    normalizedCechAugmentation_coordinate, normalizedCechAugmentation_coordinate]
  let V : X.Opens := ∏ᶜ fun b : Fin 1 => U (a b)
  let h := schemeOpen_preimage_finiteProduct f (fun b : Fin 1 => U (a b))
  change schemeModule_openEqSectionsAddEquiv M h
    (q.val.app (op (f ⁻¹ᵁ V)) (f.app V (1 : Γ(X, V)))) =
      q.val.app (op (∏ᶜ fun b : Fin 1 => f ⁻¹ᵁ U (a b)))
        (1 : Γ(Y, ∏ᶜ fun b : Fin 1 => f ⁻¹ᵁ U (a b)))
  rw [(f.app V).hom.map_one, openEq_postcomp, openEq_unit_one]

end PfaffianDescent.Coray
end
