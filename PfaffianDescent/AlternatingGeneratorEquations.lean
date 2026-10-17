import PfaffianDescent.AmbientAlternatingKernelMap

namespace PfaffianDescent
section
variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The finite list of pair evaluations defining restriction to a generated submodule. -/
def alternatingGeneratorEvaluation (v : ι → V) : AlternatingTwoForms R V →ₗ[R] (ι × ι → R) where
  toFun B ij := B ![v ij.1, v ij.2]
  map_add' B C := rfl
  map_smul' r B := rfl

lemma alternatingGeneratorEvaluation_ker (v : ι → V) :
    (alternatingGeneratorEvaluation v).ker =
      (alternatingRestriction R V (Submodule.span R (Set.range v))).ker := by
  ext B
  simp only [LinearMap.mem_ker, alternatingRestriction_span_eq_zero_iff]
  constructor
  · intro h i j
    exact congrFun h (i, j)
  · intro h
    funext ij
    exact h ij.1 ij.2

end
section
variable {R S ι : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
  (v : ι → (Fin 3 → R) × (Fin 3 → R))

lemma alternatingGeneratorEvaluation_map
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) :
    alternatingGeneratorEvaluation (graphCoefficientMap φ ∘ v) (ambientAlternatingMap φ B) =
      φ ∘ alternatingGeneratorEvaluation v B := by
  funext ij
  exact ambientAlternatingMap_apply φ B ![v ij.1, v ij.2]

end
end PfaffianDescent
