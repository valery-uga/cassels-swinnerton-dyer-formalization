import PfaffianDescent.CubicPointTraceFieldBaseChangeConstantPullback
import PfaffianDescent.FieldPointExtCoordinate

/-! # Actual original-point scalars under closed-support base change -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PfaffianDescent.BundleSectionZeroLocus
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual canonical point-support base-change map intertwines actual
residue-field multiplication and multiplication through the actual original
point projection. -/
theorem cubicPointTraceFieldBaseChangeClosedSupportIso_scalar
    {L : Type u} [Field L] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (i : Spec (.of L) ⟶ Y) [IsClosedImmersion i] (a : L) :
    (Scheme.Modules.pullback f).map (fieldPointPushforwardScalarEndomorphismAddHom i a) ≫
      (cubicPointTraceFieldBaseChangeClosedSupportIso f i).hom =
    (cubicPointTraceFieldBaseChangeClosedSupportIso f i).hom ≫
      (Scheme.Modules.pushforward (pullback.fst f i)).map
        (schemeModuleConstantEndomorphism (pullback.snd f i) a) := by
  let j := pullback.fst f i
  let g := pullback.snd f i
  let Pf := Scheme.Modules.pullback f
  let Pj := Scheme.Modules.pullback j
  let Pi := Scheme.Modules.pullback i
  let Pg := Scheme.Modules.pullback g
  let M := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  let c := schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) a
  let s := (Scheme.Modules.pushforward i).map c
  let α := pullbackSquareModuleComparison f i
  let ε := (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  let u := pullbackUnitComparison g
  let adj := Scheme.Modules.pullbackPushforwardAdjunction j
  have hnat : Pj.map (Pf.map s) ≫ α.hom.app M =
      α.hom.app M ≫ Pg.map (Pi.map s) := α.hom.naturality s
  have hε : Pi.map s ≫ ε = ε ≫ c :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).counit.naturality c
  have hu : Pg.map c ≫ u = u ≫ schemeModuleConstantEndomorphism g a := by
    simpa only [Category.comp_id] using
      cubicPointTraceFieldBaseChange_pullbackUnit_constant g (𝟙 (Spec (.of L))) a
  have ht : Pj.map (Pf.map s) ≫ (α.hom.app M ≫ Pg.map ε ≫ u) =
      (α.hom.app M ≫ Pg.map ε ≫ u) ≫ schemeModuleConstantEndomorphism g a := by
    calc
      _ = ((Pj.map (Pf.map s) ≫ α.hom.app M) ≫ Pg.map ε) ≫ u := by
        simp only [Category.assoc]
      _ = ((α.hom.app M ≫ Pg.map (Pi.map s)) ≫ Pg.map ε) ≫ u :=
        congrArg (fun v => (v ≫ Pg.map ε) ≫ u) hnat
      _ = (α.hom.app M ≫ Pg.map (Pi.map s ≫ ε)) ≫ u := by
        rw [Pg.map_comp]
        simp only [Category.assoc]
      _ = (α.hom.app M ≫ Pg.map (ε ≫ c)) ≫ u :=
        congrArg (fun v => (α.hom.app M ≫ Pg.map v) ≫ u) hε
      _ = (α.hom.app M ≫ Pg.map ε) ≫ (Pg.map c ≫ u) := by
        rw [Pg.map_comp]
        simp only [Category.assoc]
      _ = (α.hom.app M ≫ Pg.map ε) ≫ (u ≫ schemeModuleConstantEndomorphism g a) :=
        congrArg ((α.hom.app M ≫ Pg.map ε) ≫ ·) hu
      _ = _ := by simp only [Category.assoc]
  have hb : (adj.homEquiv _ _).symm
      (cubicPointTraceFieldBaseChangeClosedSupportIso f i).hom =
        α.hom.app M ≫ Pg.map ε ≫ u := by
    change (adj.homEquiv _ _).symm
      ((adj.homEquiv _ _) (α.hom.app M ≫ Pg.map ε ≫ u)) = _
    exact Equiv.symm_apply_apply _ _
  apply (adj.homEquiv _ _).symm.injective
  rw [adj.homEquiv_naturality_left_symm,
    adj.homEquiv_naturality_right_symm, hb]
  exact ht

end PfaffianDescent
