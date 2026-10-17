import PfaffianDescent.SplitRestrictionKernels
import PfaffianDescent.IncidenceAmbientCoordinates
import PfaffianDescent.IncidenceCoordinateChange
import PfaffianDescent.GrassmannianLocalModuli

namespace PfaffianDescent
open Module
section
variable (R : Type*) [CommRing R]

instance incidenceAmbientAlternating_free :
    Module.Free R (AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) :=
  Module.Free.of_equiv (alternatingCoordinates (incidenceAmbientBasis R)).symm

instance incidenceAmbientAlternating_finite :
    Module.Finite R (AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) :=
  Module.Finite.equiv (alternatingCoordinates (incidenceAmbientBasis R)).symm

/-- The restriction kernel associated to an actual locally free Grassmannian quotient. -/
abbrev IncidenceQuotientKernel
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :=
  LinearMap.ker (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) W.toSubmodule)

instance incidenceQuotientKernel_projective
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :
    Module.Projective R (IncidenceQuotientKernel R W) := by
  obtain ⟨s, hs⟩ := alternatingRestriction_split_of_projective_quotient R _ W.toSubmodule
  exact projective_kernel_of_section _ s hs

instance incidenceQuotientKernel_finite
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :
    Module.Finite R (IncidenceQuotientKernel R W) := by
  obtain ⟨s, hs⟩ := alternatingRestriction_split_of_projective_quotient R _ W.toSubmodule
  exact finite_kernel_of_section _ s hs

/-- The module of ordered isotropic triples over an arbitrary coefficient ring. -/
abbrev IncidenceQuotientFiber
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :=
  Fin 3 → IncidenceQuotientKernel R W

instance incidenceQuotientFiber_projective
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :
    Module.Projective R (IncidenceQuotientFiber R W) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype
    (R := R) (M := fun _ : Fin 3 => IncidenceQuotientKernel R W))

instance incidenceQuotientFiber_finite
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :
    Module.Finite R (IncidenceQuotientFiber R W) := inferInstance

/-- Every graph chart has twelve explicit coordinates on the actual ambient restriction kernel. -/
noncomputable def grassmannianChartKernelCoordinates
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R) :
    IncidenceQuotientKernel R (grassmannianChartQuotient R σ T) ≃ₗ[R] (IncidenceKernelIndex → R) :=
  (alternatingKernelTransportEquiv (graphCoordinatePermutation R σ.symm)
    (Matrix.toLin' T).graph (grassmannianChartSubmodule R σ T) rfl).symm.trans
      (incidenceGraphKernelCoordinates (Matrix.toLin' T))

noncomputable def grassmannianChartFiberCoordinates
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R) :
    IncidenceQuotientFiber R (grassmannianChartQuotient R σ T) ≃ₗ[R]
      (Fin 3 → IncidenceKernelIndex → R) :=
  LinearEquiv.piCongrRight (fun _ => grassmannianChartKernelCoordinates R σ T)

lemma incidenceQuotientKernel_local_free [IsLocalRing R]
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :
    Module.Free R (IncidenceQuotientKernel R W) := by
  obtain ⟨⟨σ, T⟩, rfl⟩ := grassmannianChartQuotient_surjective R 3 3 W
  exact Module.Free.of_equiv (grassmannianChartKernelCoordinates R σ T).symm

lemma incidenceQuotientKernel_local_rank [IsLocalRing R]
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :
    Module.finrank R (IncidenceQuotientKernel R W) = 12 := by
  obtain ⟨⟨σ, T⟩, rfl⟩ := grassmannianChartQuotient_surjective R 3 3 W
  rw [(grassmannianChartKernelCoordinates R σ T).finrank_eq, Module.finrank_pi, incidenceKernelIndex_card]

lemma incidenceQuotientFiber_local_rank [IsLocalRing R]
    (W : Module.Grassmannian R ((Fin 3 → R) × (Fin 3 → R)) 3) :
    Module.finrank R (IncidenceQuotientFiber R W) = 36 := by
  haveI := incidenceQuotientKernel_local_free R W
  rw [Module.finrank_pi_fintype]
  simp [incidenceQuotientKernel_local_rank]

end
end PfaffianDescent
