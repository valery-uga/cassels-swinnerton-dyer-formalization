import PfaffianDescent.IncidenceGraphCoordinates
import PfaffianDescent.AlternatingEvaluation

namespace PfaffianDescent
open Module
section
variable {R I J : Type*} [CommRing R] [Fintype I] [Fintype J]

lemma bilinearCoordinates_symm_evaluation (q : I × J → R) (x : I → R) (y : J → R) :
    (bilinearCoordinates (Pi.basisFun R I) (Pi.basisFun R J)).symm q x y =
      ∑ i, x i * (∑ j, y j * q (i, j)) := by
  classical
  change ((Pi.basisFun R I).constr R
    (fun i => (Pi.basisFun R J).constr R (fun j => q (i, j)))) x y = _
  rw [Basis.constr_apply_fintype]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, smul_eq_mul]

end

section
variable {R S I J : Type*} [CommRing R] [CommRing S] [Fintype I] [Fintype J]

lemma bilinearCoordinates_symm_map (φ : R →+* S) (q : I × J → R)
    (x : I → R) (y : J → R) :
    (bilinearCoordinates (Pi.basisFun S I) (Pi.basisFun S J)).symm (φ ∘ q)
      (φ ∘ x) (φ ∘ y) =
        φ ((bilinearCoordinates (Pi.basisFun R I) (Pi.basisFun R J)).symm q x y) := by
  simp [bilinearCoordinates_symm_evaluation, map_sum, map_mul]

end

section
variable {R : Type*} [CommRing R]

/-- Explicit polynomial formula for the form with prescribed graph-kernel coordinates. -/
lemma incidenceGraphKernelCoordinates_symm_pair
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (c : IncidenceKernelIndex → R)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    ((incidenceGraphKernelCoordinates f).symm c).1 ![x, y] =
      (bilinearCoordinates (Pi.basisFun R (Fin 3)) (Pi.basisFun R (Fin 3))).symm
        (c ∘ Sum.inl) x.1 (y.2 - f y.1) -
      (bilinearCoordinates (Pi.basisFun R (Fin 3)) (Pi.basisFun R (Fin 3))).symm
        (c ∘ Sum.inl) y.1 (x.2 - f x.1) +
      (alternatingCoordinates (Pi.basisFun R (Fin 3))).symm (c ∘ Sum.inr)
        ![x.2 - f x.1, y.2 - f y.1] := by
  change ((alternatingBlocksAssemble 0
    ((bilinearCoordinates (Pi.basisFun R (Fin 3)) (Pi.basisFun R (Fin 3))).symm
      (c ∘ Sum.inl))
    ((alternatingCoordinates (Pi.basisFun R (Fin 3))).symm (c ∘ Sum.inr))).compLinearMap
      (graphShear f).symm.toLinearMap) ![x, y] = _
  rw [alternating_comp_pair, alternatingBlocksAssemble_pair]
  simp [graphShear]

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The complete graph-kernel construction commutes with coefficient homomorphisms. -/
lemma incidenceGraphKernelCoordinates_symm_map (φ : R →+* S)
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (g : (Fin 3 → S) →ₗ[S] (Fin 3 → S))
    (hfg : ∀ x, g (φ ∘ x) = φ ∘ f x) (c : IncidenceKernelIndex → R)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    ((incidenceGraphKernelCoordinates g).symm (φ ∘ c)).1
      ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
        φ (((incidenceGraphKernelCoordinates f).symm c).1 ![x, y]) := by
  classical
  let : Fintype (Set.powersetCard (Fin 3) 2) := Fintype.ofFinite _
  have hsub (a b : Fin 3 → R) : (φ ∘ a) - (φ ∘ b) = φ ∘ (a - b) := by
    funext i
    exact (map_sub φ _ _).symm
  rw [incidenceGraphKernelCoordinates_symm_pair, incidenceGraphKernelCoordinates_symm_pair]
  dsimp only [Prod.fst, Prod.snd]
  rw [hfg, hfg, hsub, hsub]
  simp only [Function.comp_assoc]
  rw [bilinearCoordinates_symm_map φ (c ∘ Sum.inl),
    bilinearCoordinates_symm_map φ (c ∘ Sum.inl), map_add φ, map_sub φ]
  congr 1
  have h := alternatingCoordinates_symm_map φ (c ∘ Sum.inr)
    ![x.2 - f x.1, y.2 - f y.1]
  convert h using 1
  congr 1
  funext i
  fin_cases i <;> rfl

end
end PfaffianDescent
