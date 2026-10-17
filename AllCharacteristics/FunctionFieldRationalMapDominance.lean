import AllCharacteristics.GenericPointDominance

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics

universe u

/-- A function-field map to a finite-type target spreads out to a rational map
without losing the original map at the generic point. -/
theorem rationalMap_of_functionField_map
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (ybase : Y ⟶ Spec (.of k)) [LocallyOfFiniteType ybase]
    (q : Spec X.functionField ⟶ Y)
    (hq : q ≫ ybase = X.fromSpecStalk _ ≫ xbase) :
    ∃ f : X ⤏ Y, f.compHom ybase = xbase.toRationalMap ∧
      f.fromFunctionField = q := by
  let _ : X.Over (Spec (.of k)) := ⟨xbase⟩
  let _ : Y.Over (Spec (.of k)) := ⟨ybase⟩
  let _ : (Spec X.functionField).Over (Spec (.of k)) :=
    ⟨X.fromSpecStalk _ ≫ xbase⟩
  let _ : LocallyOfFiniteType (Y ↘ Spec (.of k)) := by
    change LocallyOfFiniteType ybase
    infer_instance
  have hqOver : q.IsOver (Spec (.of k)) := by
    rw [Scheme.Hom.isOver_iff]
    exact hq
  let fq : { f : Spec X.functionField ⟶ Y // f.IsOver (Spec (.of k)) } :=
    ⟨q, hqOver⟩
  let e := Scheme.RationalMap.equivFunctionFieldOver (X := X) (Y := Y)
    (S := Spec (.of k))
  let f := e fq
  refine ⟨f.1, Scheme.RationalMap.isOver_iff.mp f.2, ?_⟩
  change (e.symm f).1 = fq.1
  exact congrArg Subtype.val (e.symm_apply_apply fq)

/-- If a function-field map hits the target generic point, its spread-out
rational map is dominant. -/
theorem dominant_rationalMap_of_functionField_map
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (ybase : Y ⟶ Spec (.of k)) [LocallyOfFiniteType ybase] [IrreducibleSpace Y]
    (q : Spec X.functionField ⟶ Y)
    (hq : q ≫ ybase = X.fromSpecStalk _ ≫ xbase)
    (hqgeneric : q (genericPoint (Spec X.functionField)) = genericPoint Y) :
    ∃ f : X ⤏ Y, f.IsDominant ∧
      f.compHom ybase = xbase.toRationalMap := by
  obtain ⟨f, hfbase, hff⟩ := rationalMap_of_functionField_map xbase ybase q hq
  refine ⟨f, ?_, hfbase⟩
  apply f.isDominant_of_fromFunctionField_maps_generic
  rw [hff]
  exact hqgeneric

end AllCharacteristics
