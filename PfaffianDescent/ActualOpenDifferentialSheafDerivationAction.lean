import PfaffianDescent.ActualRelativeDifferentialSection
import PfaffianDescent.RingedSiteSheafificationComparisonUnit
import PfaffianDescent.ActualOpenImmersionDifferentialSheafIso

/- SOURCE ONLY / UNVERIFIED. The global-to-chart comparison retains the
actual universal differential section of the SAME original ring section. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k : Type u} [CommRing k] {Y X : Scheme.{u}}

lemma actualOpenImmersionDifferentialPresheafIso_D
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (CommRingCat.of k))
    (U : Y.Opens) (r : Γ(Y, U)) :
    (actualOpenImmersionDifferentialPresheafRestrictionIso f g).hom.app (op U)
      ((schemeRelativeDifferentialsPresheafDerivation (f ≫ g)).d r) =
        (schemeRelativeDifferentialsPresheafDerivation g).d ((f.appIso U).inv r) := by
  exact actualRingIsoKaehlerComparison_hom_D
    ((schemeBaseScalarPresheafMap (f ≫ g)).app (op U))
    ((schemeBaseScalarPresheafMap g).app (op (f ''ᵁ U)))
    (f.appIso U).symm (actualOpenImmersion_baseScalar_square f g U) r

-- Prove unit coherence before specializing actual scheme/site dictionaries.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringedSiteSheafificationUnitCoherence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (P : PresheafOfModules S.obj) (Q : PresheafOfModules R.obj)
    (a : P ⟶ (PresheafOfModules.pushforward φ.hom).obj Q) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app P ≫
        ((PresheafOfModules.sheafification (𝟙 S.obj)).map a).val ≫
        (moduleSheafificationRingedSiteRestrictionIso F φ Q).hom.val =
      a ≫ (PresheafOfModules.pushforward φ.hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app Q) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)
  let Q' := (PresheafOfModules.pushforward φ.hom).obj Q
  let c := (moduleSheafificationRingedSiteRestrictionIso F φ Q).hom.val
  have hn : adj.unit.app P ≫ ((PresheafOfModules.sheafification (𝟙 S.obj)).map a).val = a ≫ adj.unit.app Q' :=
    (adj.unit.naturality a).symm
  calc
    _ = (a ≫ adj.unit.app Q') ≫ c := by
      rw [← Category.assoc, hn]
    _ = a ≫ (adj.unit.app Q' ≫ c) := Category.assoc _ _ _
    _ = _ := congrArg (fun t => a ≫ t)
      (moduleSheafificationRingedSiteRestrictionIso_unit_comp F φ Q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original unit identity, inferred from abstract-site coherence with
all actual maps and conditions supplied by the genuine native construction. -/
def actualOpenImmersionDifferentialSheafIso_unit_comp
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (CommRingCat.of k)) :=
  letI := actualOpenImmersionSite_isCocontinuous f
  let φ : Y.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (_root_.Opens.grothendieckTopology Y)
        (_root_.Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
    ⟨Functor.whiskerRight (actualOpenImmersionStructurePresheafMap f)
      (forget₂ CommRingCat RingCat)⟩
  ringedSiteSheafificationUnitCoherence f.opensFunctor φ
    (schemeRelativeDifferentialsPresheaf (f ≫ g))
    (schemeRelativeDifferentialsPresheaf g)
    (actualOpenImmersionDifferentialPresheafRestrictionIso f g).hom

-- Pin the Scheme.Modules category before projecting a composite to sections.
private theorem schemeModuleComp_val_app_apply
    {Z : Scheme.{u}} {M N T : Z.Modules}
    (b : M ⟶ N) (c : N ⟶ T) (U : Z.Opens) (z : M.val.obj (op U)) :
    ((b ≫ c).val.app (op U)).hom z =
      (c.val.app (op U)).hom ((b.val.app (op U)).hom z) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOpenImmersionDifferentialSheafIso_section_D
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (CommRingCat.of k))
    (U : Y.Opens) (r : Γ(Y, U)) :
    (actualOpenImmersionDifferentialSheafRestrictionIso f g).hom.val.app (op U)
      (actualRelativeDifferentialSection (f ≫ g) U r) =
    actualRelativeDifferentialSection g (f ''ᵁ U) ((f.appIso U).inv r) := by
  let φ := Functor.whiskerRight (actualOpenImmersionStructurePresheafMap f)
    (forget₂ CommRingCat RingCat)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (schemeRelativeDifferentialsPresheaf g)
  let d := (schemeRelativeDifferentialsPresheafDerivation (f ≫ g)).d r
  let a := (actualOpenImmersionDifferentialPresheafRestrictionIso f g).hom
  have h := actualOpenImmersionDifferentialSheafIso_unit_comp f g
  have hr := congrArg (fun t => (t.app (op U)).hom d) h
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hr
  have hp :
      (((PresheafOfModules.pushforward (F := f.opensFunctor)
          (R := X.ringCatSheaf.obj) (S := Y.ringCatSheaf.obj) φ).map η).app (op U)).hom
        ((a.app (op U)).hom d) =
      (η.app (op (f ''ᵁ U))).hom ((a.app (op U)).hom d) :=
    PresheafOfModules.pushforward_map_app_apply
      (F := f.opensFunctor) (R := X.ringCatSheaf.obj) (S := Y.ringCatSheaf.obj)
      (φ := φ) η (op U) ((a.app (op U)).hom d)
  have hd := actualOpenImmersionDifferentialPresheafIso_D f g U r
  have hd' := congrArg
    (fun z : (schemeRelativeDifferentialsPresheaf g).obj (op (f ''ᵁ U)) =>
      (η.app (op (f ''ᵁ U))).hom z) hd
  have hfinal := hr.trans (hp.trans hd')
  letI := actualOpenImmersionSite_isCocontinuous f
  let φS : Y.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (_root_.Opens.grothendieckTopology Y)
        (_root_.Opens.grothendieckTopology X)).obj X.ringCatSheaf := ⟨φ⟩
  let M₀ : Y.Modules := schemeRelativeDifferentials (f ≫ g)
  let M₁ : Y.Modules :=
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
      ((PresheafOfModules.pushforward φS.hom).obj
        (schemeRelativeDifferentialsPresheaf g))
  let M₂ : Y.Modules :=
    (SheafOfModules.pushforward φS).obj (schemeRelativeDifferentials g)
  let b : M₀ ⟶ M₁ :=
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map a
  let c : M₁ ⟶ M₂ :=
    (moduleSheafificationRingedSiteRestrictionIso f.opensFunctor φS
      (schemeRelativeDifferentialsPresheaf g)).hom
  have hcomp :
      ((actualOpenImmersionDifferentialSheafRestrictionIso f g).hom.val.app (op U)).hom
        (actualRelativeDifferentialSection (f ≫ g) U r) =
      (c.val.app (op U)).hom
        ((b.val.app (op U)).hom (actualRelativeDifferentialSection (f ≫ g) U r)) := by
    change ((b ≫ c : M₀ ⟶ M₂).val.app (op U)).hom
      (actualRelativeDifferentialSection (f ≫ g) U r) = _
    exact schemeModuleComp_val_app_apply (Z := Y) b c U
      (actualRelativeDifferentialSection (f ≫ g) U r)
  refine hcomp.trans ?_
  dsimp only [actualRelativeDifferentialSection, b, c, η, d, a, φS, φ,
    Scheme.Modules.restrictFunctor, actualOpenImmersionStructurePresheafMap,
    ModuleCat.Hom.hom] at hfinal ⊢
  exact hfinal

end PfaffianDescent
