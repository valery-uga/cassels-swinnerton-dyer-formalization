import PfaffianDescent.ActualPushforwardIdealScalarZero
import PfaffianDescent.ActualRelativeDifferentialSectionAdd
import PfaffianDescent.BundleSectionZeroLocus

/- SOURCE ONLY / UNVERIFIED. The genuine universal differential on the
ACTUAL ideal is a module map after pulling to the original source. Its
Leibniz extra term vanishes by the actual ideal quotient, on every open. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [CommRing K] {X Z : Scheme.{u}}

def actualIdealUniversalDifferentialPushforward
    (g : X ⟶ Spec (.of K)) (q : Z ⟶ X)
    (J : X.Modules) (m : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hm : m ≫ closedImmersionUnitToPushforwardUnit q = 0) :
    J ⟶ (Scheme.Modules.pushforward q).obj
      ((Scheme.Modules.pullback q).obj (schemeRelativeDifferentials g)) := by
  let O := schemeRelativeDifferentials g
  let P := Scheme.Modules.pullback q
  let Q := Scheme.Modules.pushforward q
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app O
  refine { val := { app := fun U => ?_, naturality := ?_ } }
  · refine ModuleCat.ofHom
      (X := J.val.obj U)
      (Y := (Q.obj (P.obj O)).val.obj U) {
        toFun := fun z => eta.val.app U
          (actualRelativeDifferentialSection g U.unop (m.val.app U z))
        map_add' := ?_
        map_smul' := ?_ }
    · intro z w
      rw [(m.val.app U).hom.map_add,
        actualRelativeDifferentialSection_add, (eta.val.app U).hom.map_add]
    · intro r z
      let a : Γ(X, U.unop) := m.val.app U z
      let r' : Γ(X, U.unop) := r
      have ha : (closedImmersionUnitToPushforwardUnit q).val.app U a = 0 := by
        have h := congrArg (fun f => f.val.app U z) hm
        exact h
      have hz := actualPushforwardScalarZero q (P.obj O) U.unop a ha
        (eta.val.app U (actualRelativeDifferentialSection g U.unop r))
      rw [(m.val.app U).hom.map_smul]
      change eta.val.app U (actualRelativeDifferentialSection g U.unop (r' * a)) = _
      rw [actualRelativeDifferentialSection_leibniz,
        (eta.val.app U).hom.map_add,
        (eta.val.app U).hom.map_smul, (eta.val.app U).hom.map_smul, hz, add_zero]
      rfl
  · intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let hVU : V.unop ≤ U.unop := leOfHom f.unop
    have hf : f = (homOfLE hVU).op := Subsingleton.elim _ _
    rw [hf]
    change eta.val.app V
        (actualRelativeDifferentialSection g V.unop
          (m.val.app V (J.val.map (homOfLE hVU).op z))) =
      (Q.obj (P.obj O)).val.map (homOfLE hVU).op
        (eta.val.app U (actualRelativeDifferentialSection g U.unop (m.val.app U z)))
    have hmnat : m.val.app V (J.val.map (homOfLE hVU).op z) =
        X.presheaf.map (homOfLE hVU).op (m.val.app U z) :=
      PresheafOfModules.naturality_apply m.val (homOfLE hVU).op z
    have hd := actualRelativeDifferentialSection_restrict g hVU (m.val.app U z)
    exact (congrArg (fun t => eta.val.app V
        (actualRelativeDifferentialSection g V.unop t)) hmnat).trans
      ((congrArg (fun t => eta.val.app V t) hd.symm).trans
        (PresheafOfModules.naturality_apply eta.val (homOfLE hVU).op _))


lemma actualIdealUniversalDifferentialPushforward_apply
    (g : X ⟶ Spec (.of K)) (q : Z ⟶ X)
    (J : X.Modules) (m : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hm : m ≫ closedImmersionUnitToPushforwardUnit q = 0)
    (U : X.Opens) (z : J.val.obj (op U)) :
    (actualIdealUniversalDifferentialPushforward g q J m hm).val.app (op U) z =
      ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
        (schemeRelativeDifferentials g)).val.app (op U)
          (actualRelativeDifferentialSection g U (m.val.app (op U) z)) := rfl

end PfaffianDescent
