import PfaffianDescent.AlternatingTransport
import PfaffianDescent.IncidenceGraphCoordinates
import PfaffianDescent.GrassmannianTransition

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- The change of the twelve fiber coordinates induced by an ambient change
between two actual graph submodules. -/
noncomputable def incidenceKernelCoordinateChange
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (f g : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (hfg : f.graph.map e.toLinearMap = g.graph) :
    (IncidenceKernelIndex → R) ≃ₗ[R] (IncidenceKernelIndex → R) :=
  (incidenceGraphKernelCoordinates f).symm.trans
    ((alternatingKernelTransportEquiv e f.graph g.graph hfg).trans
      (incidenceGraphKernelCoordinates g))

lemma incidenceKernelCoordinateChange_reconstruct
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (f g : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (hfg : f.graph.map e.toLinearMap = g.graph)
    (c : IncidenceKernelIndex → R) :
    ((incidenceGraphKernelCoordinates g).symm (incidenceKernelCoordinateChange e f g hfg c)).1 =
      alternatingTransport e ((incidenceGraphKernelCoordinates f).symm c).1 := by
  change ((incidenceGraphKernelCoordinates g).symm
    (incidenceGraphKernelCoordinates g
      (alternatingKernelTransportEquiv e f.graph g.graph hfg
        ((incidenceGraphKernelCoordinates f).symm c)))).1 = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The fiber transition is characterized by the actual transported alternating form. -/
lemma incidenceKernelCoordinateChange_unique
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (f g : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (hfg : f.graph.map e.toLinearMap = g.graph)
    (c d : IncidenceKernelIndex → R)
    (hd : ((incidenceGraphKernelCoordinates g).symm d).1 =
      alternatingTransport e ((incidenceGraphKernelCoordinates f).symm c).1) :
    d = incidenceKernelCoordinateChange e f g hfg c := by
  apply (incidenceGraphKernelCoordinates g).symm.injective
  apply Subtype.ext
  exact hd.trans (incidenceKernelCoordinateChange_reconstruct e f g hfg c).symm

/-- Fiber coordinate changes satisfy the cocycle identity over every commutative ring. -/
theorem incidenceKernelCoordinateChange_trans
    (e d : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (f g h : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (hfg : f.graph.map e.toLinearMap = g.graph) (hgh : g.graph.map d.toLinearMap = h.graph)
    (hfh : f.graph.map (e.trans d).toLinearMap = h.graph) :
    (incidenceKernelCoordinateChange e f g hfg).trans (incidenceKernelCoordinateChange d g h hgh) =
      incidenceKernelCoordinateChange (e.trans d) f h hfh := by
  apply LinearEquiv.ext
  intro c
  apply incidenceKernelCoordinateChange_unique (e.trans d) f h hfh c
  rw [LinearEquiv.trans_apply, incidenceKernelCoordinateChange_reconstruct,
    incidenceKernelCoordinateChange_reconstruct]
  rfl

lemma incidenceKernelCoordinateChange_refl
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (hf : f.graph.map (LinearEquiv.refl R _).toLinearMap = f.graph) :
    incidenceKernelCoordinateChange (LinearEquiv.refl R _) f f hf = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro c
  symm
  apply incidenceKernelCoordinateChange_unique (LinearEquiv.refl R _) f f hf c c
  rfl

/-- The transition on all thirty-six fiber coordinates is an invertible linear map. -/
noncomputable def incidenceFiberCoordinateChange
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (f g : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (hfg : f.graph.map e.toLinearMap = g.graph) :
    (Fin 3 → IncidenceKernelIndex → R) ≃ₗ[R] (Fin 3 → IncidenceKernelIndex → R) :=
  LinearEquiv.piCongrRight (fun _ => incidenceKernelCoordinateChange e f g hfg)

lemma incidenceFiberCoordinateChange_apply
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (f g : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (hfg : f.graph.map e.toLinearMap = g.graph)
    (c : Fin 3 → IncidenceKernelIndex → R) (i : Fin 3) :
    incidenceFiberCoordinateChange e f g hfg c i = incidenceKernelCoordinateChange e f g hfg (c i) := rfl

/-- The rank-thirty-six transition maps obey the same cocycle. -/
theorem incidenceFiberCoordinateChange_trans
    (e d : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (f g h : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (hfg : f.graph.map e.toLinearMap = g.graph) (hgh : g.graph.map d.toLinearMap = h.graph)
    (hfh : f.graph.map (e.trans d).toLinearMap = h.graph) :
    (incidenceFiberCoordinateChange e f g hfg).trans (incidenceFiberCoordinateChange d g h hgh) =
      incidenceFiberCoordinateChange (e.trans d) f h hfh := by
  apply LinearEquiv.ext
  intro c
  funext i
  exact LinearEquiv.congr_fun (incidenceKernelCoordinateChange_trans e d f g h hfg hgh hfh) (c i)

/-- A standard graph overlap therefore carries an invertible linear fiber transition. -/
noncomputable def incidenceFiberGraphTransition
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (hf : Function.Bijective (graphTransitionFirst e f)) :
    (Fin 3 → IncidenceKernelIndex → R) ≃ₗ[R] (Fin 3 → IncidenceKernelIndex → R) :=
  incidenceFiberCoordinateChange e f (graphTransition e f hf) (graphTransition_map_graph e f hf)

end
end PfaffianDescent
