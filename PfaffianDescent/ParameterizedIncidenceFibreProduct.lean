import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Pulling an incidence intersection through a parameter fibre

Suppose an incidence family `U` lies in `A × P`, and `X` carries an ambient
point in `A` and a point of a parameter scheme `T → P`. Intersecting `X`
with `U` in `A × P` is canonically the same as first taking the parameter
fibre `U ×[P] T` and intersecting in `A × T`.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
variable {X U A P T : Scheme.{u}}
  (xA : X ⟶ A) (xT : X ⟶ T)
  (uA : U ⟶ A) (uP : U ⟶ P) (s : T ⟶ P)

/-- A parameterized incidence intersection is the intersection with the
parameter fibre of the incidence family. -/
noncomputable def parameterizedIncidenceFibreProductIso :
    pullback (prod.lift xA (xT ≫ s)) (prod.lift uA uP) ≅
      pullback (prod.lift xA xT)
        (prod.lift (pullback.fst uP s ≫ uA) (pullback.snd uP s)) := by
  let L := pullback (prod.lift xA (xT ≫ s)) (prod.lift uA uP)
  let Y := pullback uP s
  let R := pullback (prod.lift xA xT)
    (prod.lift (pullback.fst uP s ≫ uA) (pullback.snd uP s))
  let lX : L ⟶ X := pullback.fst _ _
  let lU : L ⟶ U := pullback.snd _ _
  have hlA : lX ≫ xA = lU ≫ uA := by
    have h := congrArg (fun z => z ≫ (prod.fst : A ⨯ P ⟶ A))
      (pullback.condition : lX ≫ prod.lift xA (xT ≫ s) =
        lU ≫ prod.lift uA uP)
    simpa only [Category.assoc, prod.lift_fst] using h
  have hlP : lU ≫ uP = (lX ≫ xT) ≫ s := by
    have h := congrArg (fun z => z ≫ (prod.snd : A ⨯ P ⟶ P))
      (pullback.condition : lX ≫ prod.lift xA (xT ≫ s) =
        lU ≫ prod.lift uA uP)
    simpa only [Category.assoc, prod.lift_snd] using h.symm
  let lY : L ⟶ Y := pullback.lift lU (lX ≫ xT) hlP
  have hlprod : lX ≫ prod.lift xA xT =
      lY ≫ prod.lift (pullback.fst uP s ≫ uA) (pullback.snd uP s) := by
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst, lY, pullback.lift_fst_assoc]
        using hlA
    · simp only [Category.assoc, prod.lift_snd, lY, pullback.lift_snd]
  let toR : L ⟶ R := pullback.lift lX lY hlprod
  let rX : R ⟶ X := pullback.fst _ _
  let rY : R ⟶ Y := pullback.snd _ _
  have hrA : rX ≫ xA = (rY ≫ pullback.fst uP s) ≫ uA := by
    have h := congrArg (fun z => z ≫ (prod.fst : A ⨯ T ⟶ A))
      (pullback.condition : rX ≫ prod.lift xA xT =
        rY ≫ prod.lift (pullback.fst uP s ≫ uA) (pullback.snd uP s))
    simpa only [Category.assoc, prod.lift_fst] using h
  have hrT : rX ≫ xT = rY ≫ pullback.snd uP s := by
    have h := congrArg (fun z => z ≫ (prod.snd : A ⨯ T ⟶ T))
      (pullback.condition : rX ≫ prod.lift xA xT =
        rY ≫ prod.lift (pullback.fst uP s ≫ uA) (pullback.snd uP s))
    simpa only [Category.assoc, prod.lift_snd] using h
  have hrP : (rX ≫ xT) ≫ s = (rY ≫ pullback.fst uP s) ≫ uP := by
    calc
      (rX ≫ xT) ≫ s = (rY ≫ pullback.snd uP s) ≫ s :=
        congrArg (· ≫ s) hrT
      _ = (rY ≫ pullback.fst uP s) ≫ uP := by
        simpa only [Category.assoc] using
          (congrArg (fun z => rY ≫ z)
            (pullback.condition : pullback.fst uP s ≫ uP =
              pullback.snd uP s ≫ s)).symm
  have hrprod : rX ≫ prod.lift xA (xT ≫ s) =
      (rY ≫ pullback.fst uP s) ≫ prod.lift uA uP := by
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using hrA
    · simpa only [Category.assoc, prod.lift_snd] using hrP
  let toL : R ⟶ L := pullback.lift rX (rY ≫ pullback.fst uP s) hrprod
  refine ⟨toR, toL, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, toR, toL, lX, rX,
        pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, toR, toL, lU, rY, lY,
        pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [Category.assoc, toR, toL, rX, lX,
        pullback.lift_fst, Category.id_comp]
    · apply pullback.hom_ext
      · simp only [Category.assoc, toR, toL, rY, lY, lU,
          pullback.lift_fst, pullback.lift_snd, Category.id_comp]
      · simp only [Category.assoc, toR, toL, rY, lY, lX, rX,
          pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]
        exact hrT

/-- The comparison leaves the point of `X` unchanged. -/
theorem parameterizedIncidenceFibreProductIso_hom_fst :
    (parameterizedIncidenceFibreProductIso xA xT uA uP s).hom ≫
      pullback.fst (prod.lift xA xT)
        (prod.lift (pullback.fst uP s ≫ uA) (pullback.snd uP s)) =
      pullback.fst (prod.lift xA (xT ≫ s)) (prod.lift uA uP) := by
  simp only [parameterizedIncidenceFibreProductIso, pullback.lift_fst]

/-- The comparison keeps the incidence point after forgetting its parameter fibre. -/
theorem parameterizedIncidenceFibreProductIso_hom_incidence :
    (parameterizedIncidenceFibreProductIso xA xT uA uP s).hom ≫
      pullback.snd (prod.lift xA xT)
        (prod.lift (pullback.fst uP s ≫ uA) (pullback.snd uP s)) ≫
          pullback.fst uP s =
      pullback.snd (prod.lift xA (xT ≫ s)) (prod.lift uA uP) := by
  simp only [parameterizedIncidenceFibreProductIso, ← Category.assoc,
    pullback.lift_snd, pullback.lift_fst]

/-- The comparison preserves the chosen point of the parameter scheme. -/
theorem parameterizedIncidenceFibreProductIso_hom_parameter :
    (parameterizedIncidenceFibreProductIso xA xT uA uP s).hom ≫
      pullback.snd (prod.lift xA xT)
        (prod.lift (pullback.fst uP s ≫ uA) (pullback.snd uP s)) ≫
          pullback.snd uP s =
      pullback.fst (prod.lift xA (xT ≫ s)) (prod.lift uA uP) ≫ xT := by
  simp only [parameterizedIncidenceFibreProductIso, ← Category.assoc,
    pullback.lift_snd]

end PfaffianDescent
