import PfaffianDescent.AlternatingGeneratorEquations

namespace PfaffianDescent
open Module

/-- Pairwise equations for the three forms on the three chart columns. -/
abbrev IncidenceEquationIndex := Fin 3 × (Fin 3 × Fin 3)

section
variable (R : Type*) [CommRing R]

/-- The actual linear restriction equations in the original forty-five ambient coefficients. -/
noncomputable def incidenceRestrictionMap
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R) :
    (AlternatingTripleIndex → R) →ₗ[R] (IncidenceEquationIndex → R) :=
  LinearMap.pi (fun i =>
    ((LinearMap.proj i.2).comp
      (alternatingGeneratorEvaluation (R := R) (grassmannianChartColumn R σ T))).comp
      ((alternatingCoordinates (incidenceAmbientBasis R)).symm.toLinearMap.comp
        (LinearMap.pi (fun s => LinearMap.proj (i.1, s)))))

lemma incidenceRestrictionMap_apply
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)
    (c : AlternatingTripleIndex → R) (i : IncidenceEquationIndex) :
    incidenceRestrictionMap R σ T c i =
      ((alternatingCoordinates (incidenceAmbientBasis R)).symm (fun s => c (i.1, s)))
        ![grassmannianChartColumn R σ T i.2.1, grassmannianChartColumn R σ T i.2.2] := rfl

/-- These linear coordinate equations express vanishing on the full actual chart submodule. -/
lemma incidenceRestrictionMap_eq_zero_iff
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)
    (c : AlternatingTripleIndex → R) :
    incidenceRestrictionMap R σ T c = 0 ↔
      ∀ k, alternatingRestriction R _ (grassmannianChartSubmodule R σ T)
        ((alternatingCoordinates (incidenceAmbientBasis R)).symm (fun s => c (k, s))) = 0 := by
  have he (k : Fin 3) := alternatingRestriction_span_eq_zero_iff (R := R)
    (grassmannianChartColumn R σ T)
    ((alternatingCoordinates (incidenceAmbientBasis R)).symm (fun s => c (k, s)))
  rw [← grassmannianChartSubmodule_span R σ T] at he
  constructor
  · intro h k
    apply (he k).mpr
    intro i j
    exact congrFun h (k, i, j)
  · intro h
    funext i
    exact (he i.1).mp (h i.1) i.2.1 i.2.2

/-- The restriction map written as a matrix, linear in the ambient form coefficients. -/
noncomputable def incidenceRestrictionMatrix
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R) :
    Matrix IncidenceEquationIndex AlternatingTripleIndex R := by
  classical
  exact LinearMap.toMatrix' (incidenceRestrictionMap R σ T)

lemma incidenceRestrictionMatrix_toLin
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R) :
    Matrix.toLin' (incidenceRestrictionMatrix R σ T) = incidenceRestrictionMap R σ T := by
  classical
  exact Matrix.toLin'_toMatrix' _

end
section
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Restriction equations commute with every coefficient homomorphism. -/
lemma incidenceRestrictionMap_map
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)
    (c : AlternatingTripleIndex → R) :
    incidenceRestrictionMap S σ (T.map φ) (φ ∘ c) = φ ∘ incidenceRestrictionMap R σ T c := by
  funext i
  rw [incidenceRestrictionMap_apply]
  rw [← grassmannianChartColumn_map φ σ T i.2.1, ← grassmannianChartColumn_map φ σ T i.2.2]
  let B := (alternatingCoordinates (incidenceAmbientBasis R)).symm (fun s => c (i.1, s))
  have he : (alternatingCoordinates (incidenceAmbientBasis S)).symm (fun s => (φ ∘ c) (i.1, s)) =
      ambientAlternatingMap φ B := by
    apply (alternatingCoordinates (incidenceAmbientBasis S)).injective
    rw [LinearEquiv.apply_symm_apply, ambientAlternatingMap_coordinates]
    rw [show B = (alternatingCoordinates (incidenceAmbientBasis R)).symm (fun s => c (i.1, s)) from rfl,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [he]
  exact ambientAlternatingMap_apply φ B
    ![grassmannianChartColumn R σ T i.2.1, grassmannianChartColumn R σ T i.2.2]

/-- The matrix entries themselves commute with scalar extension. -/
lemma incidenceRestrictionMatrix_map
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R) :
    (incidenceRestrictionMatrix R σ T).map φ = incidenceRestrictionMatrix S σ (T.map φ) := by
  classical
  funext i j
  change φ (incidenceRestrictionMap R σ T (Pi.single j 1) i) =
    incidenceRestrictionMap S σ (T.map φ) (Pi.single j 1) i
  have h := congrFun (incidenceRestrictionMap_map φ σ T (Pi.single j 1)) i
  have he : φ ∘ Pi.single j (1 : R) = Pi.single j (1 : S) := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [he] at h
  exact h.symm

end
end PfaffianDescent
