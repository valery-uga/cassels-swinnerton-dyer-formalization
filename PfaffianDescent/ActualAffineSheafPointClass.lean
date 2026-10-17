import PfaffianDescent.AffineTildeActualPointClass

/- SOURCE ONLY / UNVERIFIED. Point restriction for an ARBITRARY actual
module sheaf uses the actual pullback/pushforward adjunction unit. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

def actualAffineSheafPointClass {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : (Spec R).Modules)
    (m : (moduleSpecΓFunctor (R := R)).obj M) :
    (moduleSpecΓFunctor (R := S)).obj
      ((Scheme.Modules.pullback (Spec.map φ)).obj M) :=
  (affineGammaPushforwardNatIso φ).hom.app
    ((Scheme.Modules.pullback (Spec.map φ)).obj M)
    ((moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) m)

lemma actualAffineSheafPointClass_natural {R S : CommRingCat.{u}}
    (φ : R ⟶ S) {M N : (Spec R).Modules} (a : M ⟶ N)
    (m : (moduleSpecΓFunctor (R := R)).obj M) :
    actualAffineSheafPointClass φ N ((moduleSpecΓFunctor (R := R)).map a m) =
      (moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.pullback (Spec.map φ)).map a)
          (actualAffineSheafPointClass φ M m) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)
  have h := adj.unit.naturality a
  have hm := congrArg (fun b => (moduleSpecΓFunctor (R := R)).map b m) h
  change (moduleSpecΓFunctor (R := R)).map (adj.unit.app N)
      ((moduleSpecΓFunctor (R := R)).map a m) =
    (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pushforward (Spec.map φ)).map
        ((Scheme.Modules.pullback (Spec.map φ)).map a))
          ((moduleSpecΓFunctor (R := R)).map (adj.unit.app M) m)
  simpa only [Functor.id_map, Functor.comp_map, Functor.map_comp,
    ModuleCat.comp_apply] using hm

lemma affineTildeActualPointClass_eq_actualSheafPointClass
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) (m : M) :
    affineTildeActualPointClass φ M m =
      actualAffineSheafPointClass φ ((tilde.functor R).obj M)
        (((tilde.toTildeΓNatIso (R := R)).app M).hom m) := by
  let T := (tilde.functor R).obj M
  let P := Scheme.Modules.pullback (Spec.map φ)
  let G := moduleSpecΓFunctor (R := R)
  let adj₂ := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)
  let adj := (tilde.adjunction (R := R)).comp adj₂
  let e := affineGammaPushforwardNatIso φ
  have hUnit : (adj.ofNatIsoRight e).unit.app M =
      adj.unit.app M ≫ e.hom.app (P.obj T) := by
    rfl
  have hComp : adj.unit.app M =
      (tilde.adjunction (R := R)).unit.app M ≫ G.map (adj₂.unit.app T) :=
    Adjunction.comp_unit_app (tilde.adjunction (R := R)) adj₂ M
  have hAll : (adj.ofNatIsoRight e).unit.app M =
      (((tilde.toTildeΓNatIso (R := R)).app M).hom ≫
        G.map (adj₂.unit.app T)) ≫ e.hom.app (P.obj T) :=
    hUnit.trans (congrArg (fun a => a ≫ e.hom.app (P.obj T)) hComp)
  have hm := ConcreteCategory.congr_hom hAll m
  change (adj.ofNatIsoRight e).unit.app M m =
    e.hom.app (P.obj T)
      (G.map (adj₂.unit.app T)
        (((tilde.toTildeΓNatIso (R := R)).app M).hom m))
  exact hm

end PfaffianDescent
