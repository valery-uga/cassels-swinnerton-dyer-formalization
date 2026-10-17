import PfaffianDescent.IncidenceCoordinateRecovery
import PfaffianDescent.IncidenceTripleChart

namespace PfaffianDescent
open Module AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

/-- Coordinates for one Grassmannian graph and an arbitrary triple of ambient forms. -/
abbrev IncidenceAmbientChartRing := MvPolynomial ((Fin 3 × Fin 3) ⊕ AlternatingTripleIndex) K

noncomputable def incidenceAmbientChartMatrix : Matrix (Fin 3) (Fin 3) (IncidenceAmbientChartRing K) :=
  fun a b => MvPolynomial.X (Sum.inl (a, b))

noncomputable def incidenceAmbientChartGraph :
    (Fin 3 → IncidenceAmbientChartRing K) →ₗ[IncidenceAmbientChartRing K] (Fin 3 → IncidenceAmbientChartRing K) :=
  Matrix.toLin' (incidenceAmbientChartMatrix K)

noncomputable def incidenceAmbientChartForms (k : Fin 3) :
    AlternatingTwoForms (IncidenceAmbientChartRing K)
      ((Fin 3 → IncidenceAmbientChartRing K) × (Fin 3 → IncidenceAmbientChartRing K)) :=
  (alternatingCoordinates (incidenceAmbientBasis (IncidenceAmbientChartRing K))).symm
    (fun s => MvPolynomial.X (Sum.inr (k, s)))

/-- Restrict ambient graph-and-form coordinates to the common-isotropic incidence chart. -/
noncomputable def incidenceClosedChartAlgHom (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IncidenceAmbientChartRing K →ₐ[K] IncidenceGraphRing K :=
  MvPolynomial.aeval (Sum.elim
    (fun j => MvPolynomial.X (Sum.inl j))
    (incidenceOriginalCoefficients i (incidenceGraphUniversal K)))

lemma incidenceClosedChartAlgHom_inl (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (j : Fin 3 × Fin 3) :
    incidenceClosedChartAlgHom K i (MvPolynomial.X (Sum.inl j)) = MvPolynomial.X (Sum.inl j) :=
  MvPolynomial.aeval_X _ _

lemma incidenceClosedChartAlgHom_inr (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (j : AlternatingTripleIndex) :
    incidenceClosedChartAlgHom K i (MvPolynomial.X (Sum.inr j)) =
      incidenceOriginalCoefficients i (incidenceGraphUniversal K) j :=
  MvPolynomial.aeval_X _ _

lemma incidenceClosedChartAlgHom_graph (i : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (x : Fin 3 → IncidenceAmbientChartRing K) :
    (incidenceGraphUniversal K).1 ((incidenceClosedChartAlgHom K i) ∘ x) =
      (incidenceClosedChartAlgHom K i) ∘ incidenceAmbientChartGraph K x := by
  have hM : (incidenceAmbientChartMatrix K).map (incidenceClosedChartAlgHom K i) =
      LinearMap.toMatrix' (incidenceGraphUniversal K).1 := by
    funext a b
    have h := congrFun (incidenceGraphUniversal_coordinates K) (Sum.inl (a, b))
    exact (incidenceClosedChartAlgHom_inl K i (a, b)).trans h.symm
  have hg := congrArg Matrix.toLin' hM
  rw [Matrix.toLin'_toMatrix'] at hg
  rw [← hg]
  funext a
  exact (RingHom.map_mulVec (incidenceClosedChartAlgHom K i).toRingHom (incidenceAmbientChartMatrix K) x a).symm

lemma incidenceClosedChartAlgHom_forms (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (k : Fin 3)
    (x y : (Fin 3 → IncidenceAmbientChartRing K) × (Fin 3 → IncidenceAmbientChartRing K)) :
    incidenceOriginalForm i (incidenceGraphUniversal K) k
      ![((incidenceClosedChartAlgHom K i) ∘ x.1, (incidenceClosedChartAlgHom K i) ∘ x.2),
        ((incidenceClosedChartAlgHom K i) ∘ y.1, (incidenceClosedChartAlgHom K i) ∘ y.2)] =
      incidenceClosedChartAlgHom K i (incidenceAmbientChartForms K k ![x, y]) := by
  have hc : (incidenceClosedChartAlgHom K i).toRingHom ∘ (fun s => MvPolynomial.X (Sum.inr (k, s))) =
      alternatingCoordinates (incidenceAmbientBasis (IncidenceGraphRing K))
        (incidenceOriginalForm i (incidenceGraphUniversal K) k) := by
    funext s
    exact incidenceClosedChartAlgHom_inr K i (k, s)
  have h := incidenceAmbientCoordinates_symm_map (incidenceClosedChartAlgHom K i).toRingHom
    (fun s => MvPolynomial.X (Sum.inr (k, s))) x y
  rw [hc, LinearEquiv.symm_apply_apply] at h
  exact h

/-- Every free incidence coordinate is the restriction of a polynomial in the graph and ambient forms. -/
lemma incidenceClosedChartAlgHom_recover (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (s : IncidenceGraphIndex) :
    incidenceClosedChartAlgHom K i
      (incidenceRecoverCoordinates i (incidenceAmbientChartGraph K) (incidenceAmbientChartForms K) s) =
        MvPolynomial.X s := by
  have h := incidenceRecoverCoordinates_map (incidenceClosedChartAlgHom K i).toRingHom i
    (incidenceAmbientChartGraph K) (incidenceGraphUniversal K).1
    (incidenceClosedChartAlgHom_graph K i) (incidenceAmbientChartForms K)
    (incidenceOriginalForm i (incidenceGraphUniversal K)) (incidenceClosedChartAlgHom_forms K i)
  rw [incidenceRecoverCoordinates_actual, incidenceGraphUniversal_coordinates] at h
  exact (congrFun h s).symm

noncomputable def incidenceClosedChartRetraction (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IncidenceGraphRing K →ₐ[K] IncidenceAmbientChartRing K :=
  MvPolynomial.aeval (incidenceRecoverCoordinates i (incidenceAmbientChartGraph K) (incidenceAmbientChartForms K))

lemma incidenceClosedChartAlgHom_comp_retraction (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (incidenceClosedChartAlgHom K i).comp (incidenceClosedChartRetraction K i) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro s
  change incidenceClosedChartAlgHom K i
    ((incidenceClosedChartRetraction K i) (MvPolynomial.X s)) = MvPolynomial.X s
  rw [incidenceClosedChartRetraction, MvPolynomial.aeval_X]
  exact incidenceClosedChartAlgHom_recover K i s

/-- The ambient coordinate restriction is surjective over every coefficient ring. -/
theorem incidenceClosedChartAlgHom_surjective (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    Function.Surjective (incidenceClosedChartAlgHom K i) := by
  intro p
  exact ⟨incidenceClosedChartRetraction K i p,
    AlgHom.congr_fun (incidenceClosedChartAlgHom_comp_retraction K i) p⟩

end
end PfaffianDescent
