import PfaffianDescent.GrassmannianChartSubmodules
import PfaffianDescent.GoodPairFieldCharts

namespace PfaffianDescent

def lineChartPermutation (b : Bool) : Equiv.Perm (Fin 1 ⊕ Fin 1) :=
  if b then Equiv.sumComm (Fin 1) (Fin 1) else Equiv.refl _

section
variable (R : Type*) [CommRing R]

def lineAmbientCoordinates : ((Fin 1 → R) × (Fin 1 → R)) ≃ₗ[R] (Fin 2 → R) where
  toFun x := ![x.1 0, x.2 0]
  invFun x := (fun _ => x 0, fun _ => x 1)
  left_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' c x := by funext i; fin_cases i <;> rfl

def lineChartMatrix (a : R) : Matrix (Fin 1) (Fin 1) R := fun _ _ => a

/-- The usual two graph charts on the projective line, as actual submodules of `R²`. -/
def lineStandardSubmodule (b : Bool) (a : R) : Submodule R (Fin 2 → R) where
  carrier := {x | if b then x 0 = a * x 1 else x 1 = a * x 0}
  zero_mem' := by cases b <;> simp
  add_mem' hx hy := by
    cases b <;> simp only [Set.mem_setOf_eq, Bool.false_eq_true, ↓reduceIte, Bool.true_eq, Pi.add_apply] at hx hy ⊢ <;>
      rw [hx, hy, mul_add]
  smul_mem' c x hx := by
    cases b <;> simp only [Set.mem_setOf_eq, Bool.false_eq_true, ↓reduceIte, Bool.true_eq, Pi.smul_apply, smul_eq_mul] at hx ⊢ <;>
      rw [hx] <;> ring

lemma lineStandardSubmodule_eq_chart (b : Bool) (a : R) :
    (grassmannianChartSubmodule R (lineChartPermutation b) (lineChartMatrix R a)).map
      (lineAmbientCoordinates R).toLinearMap = lineStandardSubmodule R b a := by
  unfold grassmannianChartSubmodule
  rw [← Submodule.map_comp]
  change (Matrix.toLin' (lineChartMatrix R a)).graph.map
    ((graphCoordinatePermutation R (lineChartPermutation b).symm).trans
      (lineAmbientCoordinates R)).toLinearMap = _
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  change (((graphCoordinatePermutation R (lineChartPermutation b).symm).trans
      (lineAmbientCoordinates R)).symm x).2 =
    Matrix.toLin' (lineChartMatrix R a)
      (((graphCoordinatePermutation R (lineChartPermutation b).symm).trans
        (lineAmbientCoordinates R)).symm x).1 ↔ _
  cases b
  · change (fun _ : Fin 1 => x 1) = Matrix.toLin' (lineChartMatrix R a) (fun _ => x 0) ↔ x 1 = a * x 0
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, lineChartMatrix, funext_iff]
  · change (fun _ : Fin 1 => x 0) = Matrix.toLin' (lineChartMatrix R a) (fun _ => x 1) ↔ x 0 = a * x 1
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, lineChartMatrix, funext_iff]

lemma goodBlockMixedGraph_component (ε : Fin 3 → Bool) (u : Fin 3 → R) (i : Fin 3) :
    goodBlockSubmodule R (Fin 2 → R) (goodBlockMixedGraph R ε u) i =
      lineStandardSubmodule R (ε i) (u i) := by
  ext x
  change Pi.single i x ∈ goodBlockMixedGraph R ε u ↔
    (if ε i then x 0 = u i * x 1 else x 1 = u i * x 0)
  rw [mem_goodBlockMixedGraph]
  constructor
  · intro hx
    simpa only [Pi.single_eq_same] using hx i
  · intro hx j
    by_cases h : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hx
    · simp [Pi.single_apply, h]

end
end PfaffianDescent
