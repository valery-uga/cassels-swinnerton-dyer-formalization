import PfaffianDescent.AmbientAlternatingBaseChange
import PfaffianDescent.AlternatingSpanRestriction

namespace PfaffianDescent
open Module
section
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m n : ℕ}

lemma grassmannianSubmoduleBaseChange_span {ι : Type*} (v : ι → (Fin m → R) × (Fin n → R)) :
    grassmannianSubmoduleBaseChange φ (Submodule.span R (Set.range v)) =
      Submodule.span S (Set.range (graphCoefficientMap φ ∘ v)) := by
  rw [grassmannianSubmoduleBaseChange, span_image_span_semilinear, ← Set.range_comp]

lemma grassmannianSubmoduleBaseChange_range
    (W : Submodule R ((Fin m → R) × (Fin n → R))) :
    grassmannianSubmoduleBaseChange φ W =
      Submodule.span S (Set.range (fun x : W => graphCoefficientMap φ x.1)) := by
  rw [grassmannianSubmoduleBaseChange]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩

/-- Scalar extension preserves vanishing on the actual extended submodule. -/
lemma ambientAlternatingMap_restriction_zero
    (W : Submodule R ((Fin 3 → R) × (Fin 3 → R)))
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (hB : alternatingRestriction R _ W B = 0) :
    alternatingRestriction S _ (grassmannianSubmoduleBaseChange φ W) (ambientAlternatingMap φ B) = 0 := by
  rw [grassmannianSubmoduleBaseChange_range, alternatingRestriction_span_eq_zero_iff]
  intro x y
  change ambientAlternatingMap φ B (graphCoefficientMap φ ∘ ![x.1, y.1]) = 0
  rw [ambientAlternatingMap_apply,
    (alternatingRestriction_eq_zero_iff_pairs W B).mp hB x.1 x.2 y.1 y.2, map_zero]

/-- Coefficient extension on the actual restriction kernel. -/
noncomputable def ambientAlternatingKernelMap
    (W : Submodule R ((Fin 3 → R) × (Fin 3 → R))) :
    (alternatingRestriction R _ W).ker →ₛₗ[φ]
      (alternatingRestriction S _ (grassmannianSubmoduleBaseChange φ W)).ker :=
  ((ambientAlternatingMap φ).comp (alternatingRestriction R _ W).ker.subtype).codRestrict _
    (fun B => ambientAlternatingMap_restriction_zero φ W B.1 B.2)

lemma ambientAlternatingKernelMap_val
    (W : Submodule R ((Fin 3 → R) × (Fin 3 → R))) (B : (alternatingRestriction R _ W).ker) :
    (ambientAlternatingKernelMap φ W B).1 = ambientAlternatingMap φ B.1 := rfl

end
end PfaffianDescent
