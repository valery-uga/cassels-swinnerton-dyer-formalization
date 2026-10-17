import PfaffianDescent.AlgebraVectorIdeal
import AllCharacteristics.HomogeneousSpecialization

namespace PfaffianDescent
open MvPolynomial
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restriction to the algebra-valued line preserves homogeneous degree. -/
noncomputable def algebraLineGradedHom (p : Vec A 4) :
    homogeneousSubmodule (Fin 4) K →+*ᵍ homogeneousSubmodule Unit A where
  __ := (algebraLineHom (K := K) p).toRingHom
  map_mem := by
    intro d f hf
    change (MvPolynomial.aeval (fun j => C (p j) * X ()) f).IsHomogeneous d
    simpa only [one_mul] using hf.aeval (fun j => C (p j) * X ())
      (fun j => isHomogeneous_C_mul_X (p j) ())

/-- The homogeneous ideal underlying the algebra-valued projective coordinates. -/
noncomputable def algebraVectorHomogeneousIdeal (p : Vec A 4) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  (⊥ : HomogeneousIdeal (homogeneousSubmodule Unit A)).comap (algebraLineGradedHom p)

lemma algebraVectorHomogeneousIdeal_toIdeal (p : Vec A 4) :
    (algebraVectorHomogeneousIdeal (K := K) p).toIdeal = algebraVectorIdeal p := rfl

lemma algebraLineHom_of_homogeneous (p : Vec A 4) (f : MvPolynomial (Fin 4) K)
    {d : ℕ} (hf : f.IsHomogeneous d) :
    algebraLineHom p f = C (f.eval₂ (algebraMap K A) p) * X () ^ d := by
  have hx : (fun j => C (p j) * X ()) = (X () : MvPolynomial Unit A) • (fun j => C (p j)) := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  change f.eval₂ (C.comp (algebraMap K A)) (fun j => C (p j) * X ()) = _
  rw [hx, AllCharacteristics.eval₂_homogeneous_smul f hf, ← MvPolynomial.hom_eval₂]
  exact mul_comm _ _

/-- A homogeneous equation lies in the coordinate ideal exactly when it
vanishes on the algebra-valued coordinates. -/
theorem mem_algebraVectorIdeal_of_homogeneous (p : Vec A 4)
    (f : MvPolynomial (Fin 4) K) {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ algebraVectorIdeal (K := K) p ↔ f.eval₂ (algebraMap K A) p = 0 := by
  change algebraLineHom p f = 0 ↔ _
  rw [algebraLineHom_of_homogeneous p f hf, C_mul_X_pow_eq_monomial]
  exact monomial_eq_zero

/-- If every equation in a homogeneous ideal vanishes at algebra-valued
coordinates, the ideal is contained in the homogeneous ideal of the line
represented by those coordinates.  The decomposition into homogeneous
components is essential here: ordinary evaluation at one affine-cone point
does not detect a nonhomogeneous polynomial on the whole line. -/
theorem homogeneousIdeal_le_algebraVectorHomogeneousIdeal_of_forall_eval_zero
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : Vec A 4)
    (hzero : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K A) p = 0) :
    I ≤ algebraVectorHomogeneousIdeal (K := K) p := by
  intro f hf
  change algebraLineHom (K := K) p f = 0
  rw [← MvPolynomial.sum_homogeneousComponent f, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [algebraLineHom_of_homogeneous p (homogeneousComponent d f)
    (homogeneousComponent_isHomogeneous d f)]
  have hcomp : homogeneousComponent d f ∈ I.toIdeal := by
    rw [← decomposition.decompose'_apply]
    exact I.isHomogeneous d hf
  rw [hzero _ hcomp, C_0, zero_mul]

end

section

variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous ideal of a field-valued projective vector has no
degree-zero part, hence is contained in the irrelevant ideal. -/
theorem algebraVectorHomogeneousIdeal_le_irrelevant (p : Vec K 4) :
    algebraVectorHomogeneousIdeal (K := K) p ≤
      HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) := by
  intro f hf
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
  change ((decomposition.decompose' f 0 : homogeneousSubmodule (Fin 4) K 0) :
    MvPolynomial (Fin 4) K) = 0
  rw [decomposition.decompose'_apply, homogeneousComponent_zero, MvPolynomial.C_eq_zero]
  have hc_mem : homogeneousComponent 0 f ∈
      (algebraVectorHomogeneousIdeal (K := K) p).toIdeal := by
    rw [← decomposition.decompose'_apply]
    exact (algebraVectorHomogeneousIdeal (K := K) p).isHomogeneous 0 hf
  change algebraLineHom (K := K) p (homogeneousComponent 0 f) = 0 at hc_mem
  rw [homogeneousComponent_zero, algebraLineHom_C] at hc_mem
  exact (MvPolynomial.C_injective Unit K) (by
    simpa [Algebra.algebraMap_self] using hc_mem)

/-- A nonzero field-valued vector defines a point ideal strictly below the
irrelevant ideal. -/
theorem algebraVectorHomogeneousIdeal_lt_irrelevant_of_ne_zero
    (p : Vec K 4) (hp : p ≠ 0) :
    algebraVectorHomogeneousIdeal (K := K) p <
      HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) := by
  apply lt_of_le_not_ge (algebraVectorHomogeneousIdeal_le_irrelevant p)
  change ¬ HomogeneousIdeal.irrelevant
    (homogeneousSubmodule (Fin 4) K) ≤ vectorLineIdeal p
  exact vectorLineIdeal_not_irrelevant p hp

end
end PfaffianDescent
