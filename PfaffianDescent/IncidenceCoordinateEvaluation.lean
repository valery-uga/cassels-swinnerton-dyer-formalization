import PfaffianDescent.IncidenceGraphFormula

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- The mixed-block coordinates are evaluations on graph and complementary basis vectors. -/
lemma incidenceGraphKernelCoordinates_inl
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (B : LinearMap.ker (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph))
    (i j : Fin 3) :
    incidenceGraphKernelCoordinates f B (Sum.inl (i, j)) =
      B.1 ![(Pi.single i 1, f (Pi.single i 1)), (0, Pi.single j 1)] := by
  change (B.1.compLinearMap (graphShear f).toLinearMap)
    ![(Pi.basisFun R (Fin 3) i, 0), (0, Pi.basisFun R (Fin 3) j)] = _
  rw [Pi.basisFun_apply, Pi.basisFun_apply, alternating_comp_pair]
  congr 1
  funext k
  fin_cases k <;> simp [graphShear]

/-- The remaining coordinates evaluate the form on the complementary summand. -/
lemma incidenceGraphKernelCoordinates_inr
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (B : LinearMap.ker (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph))
    (s : Set.powersetCard (Fin 3) 2) :
    incidenceGraphKernelCoordinates f B (Sum.inr s) =
      B.1 (fun k => (0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s k) 1)) := by
  change alternatingCoordinates (Pi.basisFun R (Fin 3))
    ((B.1.compLinearMap (graphShear f).toLinearMap).compLinearMap
      (LinearMap.inr R (Fin 3 → R) (Fin 3 → R))) s = _
  rw [alternatingCoordinates_apply]
  simp only [AlternatingMap.compLinearMap_apply, Function.comp_apply, Pi.basisFun_apply]
  change B.1 (fun k => (0, f 0 + Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s k) 1)) = _
  simp only [map_zero, zero_add]

lemma incidenceGraphKernelCoordinates_inr_pair
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (B : LinearMap.ker (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph))
    (s : Set.powersetCard (Fin 3) 2) :
    incidenceGraphKernelCoordinates f B (Sum.inr s) = B.1
      ![(0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s 0) 1),
        (0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s 1) 1)] := by
  rw [incidenceGraphKernelCoordinates_inr]
  congr 1
  funext k
  fin_cases k <;> rfl

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma ringHom_comp_single_one (φ : R →+* S) (i : Fin 3) :
    φ ∘ Pi.single i (1 : R) = Pi.single i (1 : S) := by
  funext j
  by_cases h : j = i <;> simp [h]

lemma ringHom_comp_zero (φ : R →+* S) : φ ∘ (0 : Fin 3 → R) = (0 : Fin 3 → S) := by
  funext j
  exact φ.map_zero

/-- Forward fiber coordinates commute with coefficient maps whenever the actual
forms and their graph maps do so. -/
lemma incidenceGraphKernelCoordinates_map (φ : R →+* S)
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (g : (Fin 3 → S) →ₗ[S] (Fin 3 → S))
    (hfg : ∀ x, g (φ ∘ x) = φ ∘ f x)
    (B : LinearMap.ker (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph))
    (C : LinearMap.ker (alternatingRestriction S ((Fin 3 → S) × (Fin 3 → S)) g.graph))
    (hBC : ∀ x y : (Fin 3 → R) × (Fin 3 → R),
      C.1 ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] = φ (B.1 ![x, y])) :
    incidenceGraphKernelCoordinates g C = φ ∘ incidenceGraphKernelCoordinates f B := by
  funext s
  rcases s with ⟨i, j⟩ | s
  · rw [incidenceGraphKernelCoordinates_inl]
    change _ = φ (incidenceGraphKernelCoordinates f B (Sum.inl (i, j)))
    rw [incidenceGraphKernelCoordinates_inl]
    have h := hBC (Pi.single i 1, f (Pi.single i 1)) (0, Pi.single j 1)
    have hf := hfg (Pi.single i 1)
    rw [ringHom_comp_single_one] at hf
    simpa only [Prod.fst, Prod.snd, ringHom_comp_single_one, ringHom_comp_zero, ← hf] using h
  · rw [incidenceGraphKernelCoordinates_inr_pair]
    change _ = φ (incidenceGraphKernelCoordinates f B (Sum.inr s))
    rw [incidenceGraphKernelCoordinates_inr_pair]
    have h := hBC (0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s 0) 1)
      (0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s 1) 1)
    simpa only [Prod.fst, Prod.snd, ringHom_comp_single_one, ringHom_comp_zero] using h

end
end PfaffianDescent
