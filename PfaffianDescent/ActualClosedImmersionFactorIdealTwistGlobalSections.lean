import PfaffianDescent.ActualClosedImmersionFactorIdealTwistRestriction
import PfaffianDescent.CubicPointTraceFieldBaseChangeConstantPullback

/- SOURCE ONLY / UNVERIFIED. Actual K-linear restriction of GENUINE
ambient ideal-twist global sections to the original subscheme ideal and
the literal pulled-back ambient twist. Every geometric map is derived. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] isIso_pullbackUnitComparison

def actualClosedImmersionFactorIdealTwistGlobalSectionsRestriction
    {K : Type u} [Field K] {Y X Z : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (i : X ⟶ Y) (q : Z ⟶ X)
    [IsClosedImmersion q] [IsClosedImmersion (q ≫ i)] (T : Y.Modules) :
    SchemeModuleGlobalSectionsOver g (schemeModuleTensor (closedImmersionModule (q ≫ i)) T) →ₗ[K]
      SchemeModuleGlobalSectionsOver (i ≫ g)
        (schemeModuleTensor (closedImmersionModule q) ((Scheme.Modules.pullback i).obj T)) where
  toFun s := by
    letI : IsIso (pullbackUnitComparison i) := isIso_pullbackUnitComparison i
    exact inv (pullbackUnitComparison i) ≫ (Scheme.Modules.pullback i).map s ≫
      actualClosedImmersionFactorIdealTwistRestriction i q T
  map_add' s t := by
    let P := Scheme.Modules.pullback i
    letI : IsIso (pullbackUnitComparison i) := isIso_pullbackUnitComparison i
    let v := inv (pullbackUnitComparison i)
    let r := actualClosedImmersionFactorIdealTwistRestriction i q T
    change v ≫ P.map (s + t) ≫ r = v ≫ P.map s ≫ r + v ≫ P.map t ≫ r
    calc
      _ = v ≫ (P.map s + P.map t) ≫ r :=
        congrArg (fun m => v ≫ m ≫ r) (P.map_add (f := s) (g := t))
      _ = v ≫ (P.map s ≫ r + P.map t ≫ r) :=
        congrArg (fun m => v ≫ m) (Preadditive.add_comp (C := X.Modules) _ _ _ (P.map s) (P.map t) r)
      _ = _ := Preadditive.comp_add (C := X.Modules) _ _ _ v (P.map s ≫ r) (P.map t ≫ r)
  map_smul' c s := by
    let P := Scheme.Modules.pullback i
    let u := pullbackUnitComparison i
    letI : IsIso u := isIso_pullbackUnitComparison i
    have hu : inv u ≫ P.map (schemeModuleConstantEndomorphism g c) =
        schemeModuleConstantEndomorphism (i ≫ g) c ≫ inv u := by
      apply (cancel_mono u).1
      have hn : P.map (schemeModuleConstantEndomorphism g c) ≫ u =
          u ≫ schemeModuleConstantEndomorphism (i ≫ g) c :=
        cubicPointTraceFieldBaseChange_pullbackUnit_constant i g c
      calc
        (inv u ≫ P.map (schemeModuleConstantEndomorphism g c)) ≫ u =
            inv u ≫ (u ≫ schemeModuleConstantEndomorphism (i ≫ g) c) := by
          rw [Category.assoc, hn]
        _ = schemeModuleConstantEndomorphism (i ≫ g) c := by
          rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
        _ = (schemeModuleConstantEndomorphism (i ≫ g) c ≫ inv u) ≫ u := by
          rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    let a := schemeModuleConstantEndomorphism g c
    let b := schemeModuleConstantEndomorphism (i ≫ g) c
    let r := actualClosedImmersionFactorIdealTwistRestriction i q T
    change inv u ≫ P.map (a ≫ s) ≫ r = b ≫ inv u ≫ P.map s ≫ r
    calc
      _ = inv u ≫ (P.map a ≫ P.map s) ≫ r :=
        congrArg (fun m => inv u ≫ m ≫ r) (P.map_comp a s)
      _ = (inv u ≫ P.map a) ≫ (P.map s ≫ r) :=
        (congrArg (fun m => inv u ≫ m) (Category.assoc (P.map a) (P.map s) r)).trans
          (Category.assoc (inv u) (P.map a) (P.map s ≫ r)).symm
      _ = (b ≫ inv u) ≫ (P.map s ≫ r) :=
        congrArg (fun m => m ≫ (P.map s ≫ r)) hu
      _ = b ≫ inv u ≫ P.map s ≫ r := Category.assoc _ _ _

end PfaffianDescent
