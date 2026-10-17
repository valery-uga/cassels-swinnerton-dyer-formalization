import PfaffianDescent.IncidenceCoordinateChange
import PfaffianDescent.IncidenceGraphFunctor
import PfaffianDescent.GrassmannianTransitionCocycle

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

lemma incidenceGraphPoint_ext (p q : IncidenceGraphPoints R) (hf : p.1 = q.1)
    (hB : ∀ i : Fin 3, (p.2 i).1 = (q.2 i).1) : p = q := by
  rcases p with ⟨f, B⟩
  rcases q with ⟨g, C⟩
  dsimp only at hf hB
  subst g
  congr 1
  funext i
  exact Subtype.ext (hB i)

/-- Change graph coordinates and simultaneously transport the three alternating
forms. The output is again an actual common-isotropic incidence point. -/
noncomputable def incidencePointTransition
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (p : IncidenceGraphPoints R) (hp : Function.Bijective (graphTransitionFirst e p.1)) :
    IncidenceGraphPoints R :=
  ⟨graphTransition e p.1 hp, fun i =>
    alternatingKernelTransportEquiv e p.1.graph (graphTransition e p.1 hp).graph
      (graphTransition_map_graph e p.1 hp) (p.2 i)⟩

lemma incidencePointTransition_graph
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (p : IncidenceGraphPoints R) (hp : Function.Bijective (graphTransitionFirst e p.1)) :
    (incidencePointTransition e p hp).1 = graphTransition e p.1 hp := rfl

lemma incidencePointTransition_form
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (p : IncidenceGraphPoints R) (hp : Function.Bijective (graphTransitionFirst e p.1)) (i : Fin 3) :
    ((incidencePointTransition e p hp).2 i).1 = alternatingTransport e (p.2 i).1 := rfl

lemma incidencePointTransition_refl (p : IncidenceGraphPoints R)
    (hp : Function.Bijective (graphTransitionFirst (LinearEquiv.refl R _) p.1)) :
    incidencePointTransition (LinearEquiv.refl R _) p hp = p := by
  apply incidenceGraphPoint_ext
  · exact graphTransition_refl p.1 hp
  · intro i
    rfl

/-- The full incidence transition has an inverse, including its actual forms. -/
theorem incidencePointTransition_inverse
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (p : IncidenceGraphPoints R) (hp : Function.Bijective (graphTransitionFirst e p.1)) :
    incidencePointTransition e.symm (incidencePointTransition e p hp)
      (graphTransition_inverse_overlap e p.1 hp) = p := by
  apply incidenceGraphPoint_ext
  · exact graphTransition_inverse e p.1 hp
  · intro i
    exact (alternatingTransport e).symm_apply_apply (p.2 i).1

/-- The full incidence transitions satisfy the cocycle, not only their graph matrices. -/
theorem incidencePointTransition_cocycle
    (e d : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (p : IncidenceGraphPoints R) (he : Function.Bijective (graphTransitionFirst e p.1))
    (hd : Function.Bijective (graphTransitionFirst d (incidencePointTransition e p he).1))
    (hed : Function.Bijective (graphTransitionFirst (e.trans d) p.1)) :
    incidencePointTransition d (incidencePointTransition e p he) hd =
      incidencePointTransition (e.trans d) p hed := by
  apply incidenceGraphPoint_ext
  · exact graphTransition_cocycle e d p.1 he hd hed
  · intro i
    rfl

lemma incidencePointTransition_coordinate_inl
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (p : IncidenceGraphPoints R) (hp : Function.Bijective (graphTransitionFirst e p.1)) (i j : Fin 3) :
    incidenceGraphPointCoordinates R (incidencePointTransition e p hp) (Sum.inl (i, j)) =
      LinearMap.toMatrix' (graphTransition e p.1 hp) i j := rfl

/-- On each fixed graph the transition is exactly the invertible linear fiber map. -/
lemma incidencePointTransition_coordinate_inr
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (p : IncidenceGraphPoints R) (hp : Function.Bijective (graphTransitionFirst e p.1))
    (i : Fin 3) (s : IncidenceKernelIndex) :
    incidenceGraphPointCoordinates R (incidencePointTransition e p hp) (Sum.inr (i, s)) =
      incidenceKernelCoordinateChange e p.1 (graphTransition e p.1 hp)
        (graphTransition_map_graph e p.1 hp) (incidenceGraphKernelCoordinates p.1 (p.2 i)) s := by
  change incidenceGraphKernelCoordinates _
      (alternatingKernelTransportEquiv e p.1.graph _ (graphTransition_map_graph e p.1 hp) (p.2 i)) s =
    incidenceGraphKernelCoordinates _
      (alternatingKernelTransportEquiv e p.1.graph _ (graphTransition_map_graph e p.1 hp)
        ((incidenceGraphKernelCoordinates p.1).symm (incidenceGraphKernelCoordinates p.1 (p.2 i)))) s
  rw [LinearEquiv.symm_apply_apply]

end
end PfaffianDescent
