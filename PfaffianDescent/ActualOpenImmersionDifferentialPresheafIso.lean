import PfaffianDescent.ActualRingIsoKaehlerComparison
import PfaffianDescent.ActualOpenImmersionScalarSquare

/- SOURCE ONLY / UNVERIFIED. Canonical differential-presheaf comparison
for any actual open immersion, including the native Spec(chart ring). -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k : Type u} [CommRing k] {Y X : Scheme.{u}}

def actualOpenImmersionStructurePresheafMap (f : Y ⟶ X) [IsOpenImmersion f] :
    Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf where
  app U := (f.appIso U.unop).inv
  naturality {U V} i := f.appIso_inv_naturality i

-- Ring naturality is evaluated through the explicit CommRingCat.Hom.hom
-- projection before entering any differential-module context.
private theorem ringPresheafIso_hom_naturality
    {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D)
    (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (e : S ≅ F.op ⋙ R) {U V : Cᵒᵖ} (i : U ⟶ V) (r : S.obj U) :
    (e.hom.app V).hom ((S.map i).hom r) =
      (R.map (F.op.map i)).hom ((e.hom.app U).hom r) := by
  have hn : S.map i ≫ e.hom.app V =
      e.hom.app U ≫ R.map (F.op.map i) := e.hom.naturality i
  exact congrArg (fun t : S.obj U ⟶ R.obj (F.op.obj V) => t.hom r) hn

-- Fix the module-presheaf base before elaborating any isomorphism result.
private def differentialRingPresheafData
    {C : Type u} [Category C] (B : CommRingCat.{u})
    (S : Cᵒᵖ ⥤ CommRingCat.{u})
    (α : (Functor.const Cᵒᵖ).obj B ⟶ S) :
    PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' α

private def differentialRingPresheafPushforwardData
    {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (B : CommRingCat.{u})
    (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (e : S ≅ F.op ⋙ R)
    (α' : (Functor.const Dᵒᵖ).obj B ⟶ R) :
    PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pushforward (F := F)
    (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat)
    (Functor.whiskerRight e.hom (forget₂ CommRingCat RingCat))).obj
      (differentialRingPresheafData B R α')

-- Normalize only the installed object reboxing before exposing a component to isoMk.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def differentialRingPresheafIsoComponent
    {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (B : CommRingCat.{u})
    (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (e : S ≅ F.op ⋙ R)
    (α : (Functor.const Cᵒᵖ).obj B ⟶ S)
    (α' : (Functor.const Dᵒᵖ).obj B ⟶ R)
    (hbase : ∀ U : Cᵒᵖ, α.app U ≫ (e.app U).hom = α'.app (F.op.obj U))
    (U : Cᵒᵖ) :
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' α).obj U ≅
      ((PresheafOfModules.pushforward
        (Functor.whiskerRight e.hom (forget₂ CommRingCat RingCat))).obj
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' α')).obj U := by
  let c := actualRingIsoKaehlerComparison (α.app U) (α'.app (F.op.obj U))
    (e.app U) (hbase U)
  -- All these declarations are installed object constructors. Their .obj
  -- projections discard map/proof fields; the comparison factory stays opaque.
  dsimp only [PresheafOfModules.DifferentialsConstruction.relativeDifferentials',
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj, Functor.comp_obj,
    Functor.whiskerRight, Iso.app, ModuleCat.of] at c ⊢
  exact c

-- This statement mentions only typed DATA objects over the SAME explicit ring functor.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem differentialRingPresheafIsoComponent_naturality
    {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (B : CommRingCat.{u})
    (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (e : S ≅ F.op ⋙ R)
    (α : (Functor.const Cᵒᵖ).obj B ⟶ S)
    (α' : (Functor.const Dᵒᵖ).obj B ⟶ R)
    (hbase : ∀ U : Cᵒᵖ, α.app U ≫ (e.app U).hom = α'.app (F.op.obj U))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (differentialRingPresheafData B S α).map i ≫
        (ModuleCat.restrictScalars
          (((S ⋙ forget₂ CommRingCat RingCat).map i).hom)).map
          (differentialRingPresheafIsoComponent F B S R e α α' hbase V).hom =
      (differentialRingPresheafIsoComponent F B S R e α α' hbase U).hom ≫
        (differentialRingPresheafPushforwardData F B S R e α').map i := by
  let M := differentialRingPresheafData B R α'
  let P := differentialRingPresheafPushforwardData F B S R e α'
  apply CommRingCat.KaehlerDifferential.ext
  intro r
  change
    (actualRingIsoKaehlerComparison (α.app V) (α'.app (F.op.obj V))
      (e.app V) (hbase V)).hom
      (((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' α).map i).hom
        (CommRingCat.KaehlerDifferential.d (f := α.app U) r)) =
    (P.map i).hom
      ((actualRingIsoKaehlerComparison (α.app U) (α'.app (F.op.obj U))
        (e.app U) (hbase U)).hom
        (CommRingCat.KaehlerDifferential.d (f := α.app U) r))
  have hring : ((e.app V).hom).hom ((S.map i).hom r) =
      (R.map (F.op.map i)).hom (((e.app U).hom).hom r) :=
    ringPresheafIso_hom_naturality F S R e i r
  calc
    _ = (actualRingIsoKaehlerComparison (α.app V) (α'.app (F.op.obj V))
        (e.app V) (hbase V)).hom
        (CommRingCat.KaehlerDifferential.d (f := α.app V) (S.map i r)) :=
      congrArg
        (fun z => (actualRingIsoKaehlerComparison (α.app V) (α'.app (F.op.obj V))
          (e.app V) (hbase V)).hom z)
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d α i r)
    _ = CommRingCat.KaehlerDifferential.d (f := α'.app (F.op.obj V))
        ((e.app V).hom (S.map i r)) :=
      actualRingIsoKaehlerComparison_hom_D (α.app V) (α'.app (F.op.obj V))
        (e.app V) (hbase V) (S.map i r)
    _ = CommRingCat.KaehlerDifferential.d (f := α'.app (F.op.obj V))
        (R.map (F.op.map i) ((e.app U).hom r)) :=
      congrArg (fun z : R.obj (F.op.obj V) =>
        CommRingCat.KaehlerDifferential.d (f := α'.app (F.op.obj V)) z) hring
    _ = (M.map (F.op.map i)).hom
        (CommRingCat.KaehlerDifferential.d (f := α'.app (F.op.obj U))
          ((e.app U).hom r)) :=
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d
        α' (F.op.map i) ((e.app U).hom r)).symm
    _ = (P.map i).hom
        (CommRingCat.KaehlerDifferential.d (f := α'.app (F.op.obj U))
          ((e.app U).hom r)) :=
      (PresheafOfModules.pushforward_obj_map_apply
        (Functor.whiskerRight e.hom (forget₂ CommRingCat RingCat)) M i
        (CommRingCat.KaehlerDifferential.d (f := α'.app (F.op.obj U))
          ((e.app U).hom r))).symm
    _ = _ := congrArg (fun z => (P.map i).hom z)
      (actualRingIsoKaehlerComparison_hom_D (α.app U) (α'.app (F.op.obj U))
        (e.app U) (hbase U) r).symm

-- Pure inferred Iso application: no rich manually duplicated return type.
private def differentialPresheafIsoOfRingPresheafIso
    {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (B : CommRingCat.{u})
    (S : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (e : S ≅ F.op ⋙ R)
    (α : (Functor.const Cᵒᵖ).obj B ⟶ S)
    (α' : (Functor.const Dᵒᵖ).obj B ⟶ R)
    (hbase : ∀ U : Cᵒᵖ, α.app U ≫ (e.app U).hom = α'.app (F.op.obj U)) :=
  PresheafOfModules.isoMk
    (M₁ := differentialRingPresheafData B S α)
    (M₂ := differentialRingPresheafPushforwardData F B S R e α')
    (fun U => differentialRingPresheafIsoComponent F B S R e α α' hbase U)
    (fun {U V} i => differentialRingPresheafIsoComponent_naturality F B S R e α α' hbase i)

private def openImmersionStructurePresheafIso
    (f : Y ⟶ X) [IsOpenImmersion f] : Y.presheaf ≅ f.opensFunctor.op ⋙ X.presheaf :=
  NatIso.ofComponents (fun U => (f.appIso U.unop).symm)
    (fun i => f.appIso_inv_naturality i)

private theorem openImmersionStructurePresheafIso_hom
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (openImmersionStructurePresheafIso f).hom =
      actualOpenImmersionStructurePresheafMap f := rfl

/-- The actual comparison is inferred from the generic constructor. Its
objectwise maps remain the SAME inverse appIso Kaehler comparisons. -/
def actualOpenImmersionDifferentialPresheafRestrictionIso
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (CommRingCat.of k)) :=
  differentialPresheafIsoOfRingPresheafIso f.opensFunctor (CommRingCat.of k)
    Y.presheaf X.presheaf (openImmersionStructurePresheafIso f)
    (schemeBaseScalarPresheafMap (f ≫ g)) (schemeBaseScalarPresheafMap g)
    (fun U => actualOpenImmersion_baseScalar_square f g U.unop)

end PfaffianDescent
