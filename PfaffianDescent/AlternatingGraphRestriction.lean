import PfaffianDescent.IncidenceGraphCoordinates

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- Vanishing of an alternating form on a graph is equivalent to vanishing of
its entries on the graph basis, over arbitrary commutative rings. -/
lemma alternatingRestriction_graph_eq_zero_iff
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) :
    alternatingRestriction R _ f.graph B = 0 ↔
      ∀ i j : Fin 3, B ![(Pi.single i 1, f (Pi.single i 1)),
        (Pi.single j 1, f (Pi.single j 1))] = 0 := by
  constructor
  · intro h i j
    have hh := DFunLike.congr_fun h
      ![⟨(Pi.single i 1, f (Pi.single i 1)), rfl⟩,
        ⟨(Pi.single j 1, f (Pi.single j 1)), rfl⟩]
    change (B.compLinearMap f.graph.subtype) _ = 0 at hh
    rw [alternating_comp_pair] at hh
    exact hh
  · intro h
    let e : (Fin 3 → R) →ₗ[R] ((Fin 3 → R) × (Fin 3 → R)) := LinearMap.id.prod f
    let Q := (alternatingBilinear B).compl₁₂ e e
    have hQ : Q = 0 := by
      apply (Pi.basisFun R (Fin 3)).ext
      intro i
      apply (Pi.basisFun R (Fin 3)).ext
      intro j
      simpa [Q, e] using h i j
    ext v
    change B (fun i => (v i).1) = 0
    have heta : (fun i => (v i).1) = ![(v 0).1, (v 1).1] := by
      funext i
      fin_cases i <;> rfl
    rw [heta]
    have hv (i : Fin 2) : (v i).1 = ((v i).1.1, f (v i).1.1) :=
      Prod.ext rfl (v i).2
    rw [hv 0, hv 1]
    exact LinearMap.congr_fun (LinearMap.congr_fun hQ (v 0).1.1) (v 1).1.1

end
end PfaffianDescent
