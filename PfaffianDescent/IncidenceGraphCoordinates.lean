import PfaffianDescent.AlternatingGraph

namespace PfaffianDescent
open Module

section
variable {R M N I J : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- A bilinear block has one independent coefficient for each pair of basis vectors. -/
noncomputable def bilinearCoordinates (b : Basis I R M) (c : Basis J R N) :
    (M →ₗ[R] N →ₗ[R] R) ≃ₗ[R] (I × J → R) :=
  ((b.constr R).symm.trans (LinearEquiv.piCongrRight (fun _ => (c.constr R).symm))).trans
    { toFun := fun f ij => f ij.1 ij.2
      invFun := fun f i j => f (i, j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] lemma bilinearCoordinates_apply (b : Basis I R M) (c : Basis J R N)
    (Q : M →ₗ[R] N →ₗ[R] R) (ij : I × J) :
    bilinearCoordinates b c Q ij = Q (b ij.1) (c ij.2) := rfl

end

/-- The twelve coefficients left after an alternating form vanishes on a graph. -/
abbrev IncidenceKernelIndex := (Fin 3 × Fin 3) ⊕ Set.powersetCard (Fin 3) 2

noncomputable instance : Fintype IncidenceKernelIndex := Fintype.ofFinite _

lemma incidenceKernelIndex_card : Fintype.card IncidenceKernelIndex = 12 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card ((Fin 3 × Fin 3) ⊕ Set.powersetCard (Fin 3) 2) = 12
  rw [Nat.card_sum, Nat.card_prod, Set.powersetCard.card]
  norm_num [Nat.choose]

section
variable {R : Type*} [CommRing R]

/-- Explicit free coordinates on the rank-twelve restriction kernel over a
standard Grassmannian chart, with no field or reducedness hypothesis. -/
noncomputable def incidenceGraphKernelCoordinates
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) :
    LinearMap.ker (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph) ≃ₗ[R]
      (IncidenceKernelIndex → R) :=
  (alternatingGraphKernelEquiv f).trans
    ((LinearEquiv.prodCongr
      (bilinearCoordinates (Pi.basisFun R (Fin 3)) (Pi.basisFun R (Fin 3)))
      (alternatingCoordinates (Pi.basisFun R (Fin 3)))).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ R R).symm)

instance incidenceGraphKernel_free (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) :
    Module.Free R (LinearMap.ker
      (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph)) :=
  Module.Free.of_equiv (incidenceGraphKernelCoordinates f).symm

instance incidenceGraphKernel_finite (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) :
    Module.Finite R (LinearMap.ker
      (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph)) :=
  Module.Finite.equiv (incidenceGraphKernelCoordinates f).symm

lemma incidenceGraphKernel_rank_twelve [Nontrivial R]
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) :
    finrank R (LinearMap.ker
      (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph)) = 12 := by
  rw [(incidenceGraphKernelCoordinates f).finrank_eq, Module.finrank_pi, incidenceKernelIndex_card]

/-- Ordered triples of forms vanishing on a graph, as a module. -/
abbrev IncidenceGraphFiber (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) :=
  Fin 3 → LinearMap.ker (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph)

/-- The rank-thirty-six fiber has explicit coordinates over every coefficient ring. -/
noncomputable def incidenceGraphFiberCoordinates
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) :
    IncidenceGraphFiber f ≃ₗ[R] (Fin 3 → IncidenceKernelIndex → R) :=
  LinearEquiv.piCongrRight (fun _ => incidenceGraphKernelCoordinates f)

lemma incidenceGraphFiber_rank_thirtysix [Nontrivial R]
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) :
    finrank R (IncidenceGraphFiber f) = 36 := by
  rw [Module.finrank_pi_fintype]
  simp [incidenceGraphKernel_rank_twelve]

end
end PfaffianDescent
