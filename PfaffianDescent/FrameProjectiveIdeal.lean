import PfaffianDescent.FrameCoordinateRingExact
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def frameLineVariableMV (p : Option (Fin 4)) (i : Fin 4) : MvPolynomial Unit K :=
  match p with
  | none => X ()
  | some j => if i = j then X () else 0

lemma frameLineVariableMV_homogeneous (p : Option (Fin 4)) (i : Fin 4) :
    (frameLineVariableMV (K := K) p i).IsHomogeneous 1 := by
  cases p with
  | none => exact isHomogeneous_X K ()
  | some j =>
      by_cases h : i = j
      · simp only [frameLineVariableMV, h, ↓reduceIte]
        exact isHomogeneous_X K ()
      · simp only [frameLineVariableMV, h, ↓reduceIte]
        exact (homogeneousSubmodule Unit K 1).zero_mem

noncomputable def frameLineGradedHom (p : Option (Fin 4)) :
    homogeneousSubmodule (Fin 4) K →+*ᵍ homogeneousSubmodule Unit K where
  __ := (MvPolynomial.aeval (frameLineVariableMV (K := K) p)).toRingHom
  map_mem := by
    intro n f hf
    change (MvPolynomial.aeval (frameLineVariableMV (K := K) p) f).IsHomogeneous n
    have h := hf.aeval (frameLineVariableMV (K := K) p) (frameLineVariableMV_homogeneous p)
    simpa only [one_mul] using h

noncomputable def frameLineHomogeneousIdeal (p : Option (Fin 4)) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  (⊥ : HomogeneousIdeal (homogeneousSubmodule Unit K)).comap (frameLineGradedHom p)

lemma mem_frameLineHomogeneousIdeal (p : Option (Fin 4)) (f : MvPolynomial (Fin 4) K) :
    f ∈ frameLineHomogeneousIdeal (K := K) p ↔ MvPolynomial.aeval (frameLineVariableMV (K := K) p) f = 0 :=
  Iff.rfl

instance frameLineHomogeneousIdeal_prime (p : Option (Fin 4)) :
    (frameLineHomogeneousIdeal (K := K) p).toIdeal.IsPrime := by
  change (Ideal.comap (frameLineGradedHom (K := K) p).toRingHom
    (⊥ : Ideal (MvPolynomial Unit K))).IsPrime
  infer_instance

lemma frameLineHomogeneousIdeal_not_irrelevant (p : Option (Fin 4)) :
    ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤
      frameLineHomogeneousIdeal p := by
  intro h
  have hm (j : Fin 4) : (X j : MvPolynomial (Fin 4) K) ∈ frameLineHomogeneousIdeal p :=
    h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1) (isHomogeneous_X K j))
  cases p with
  | none =>
      have he := (mem_frameLineHomogeneousIdeal none (X 0)).mp (hm 0)
      exact X_ne_zero () (by simpa only [aeval_X, frameLineVariableMV] using he)
  | some j =>
      have he := (mem_frameLineHomogeneousIdeal (some j) (X j)).mp (hm j)
      exact X_ne_zero () (by simpa only [aeval_X, frameLineVariableMV, ↓reduceIte] using he)

/-- The five displayed frame points, as actual points of projective three-space. -/
noncomputable def frameProjectivePoint (p : Option (Fin 4)) :
    ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) where
  asHomogeneousIdeal := frameLineHomogeneousIdeal p
  isPrime := inferInstance
  not_irrelevant_le := frameLineHomogeneousIdeal_not_irrelevant p

lemma frameLine_eval_comparison (p : Option (Fin 4)) :
    (MvPolynomial.uniqueAlgEquiv K Unit).toAlgHom.comp
      (MvPolynomial.aeval (frameLineVariableMV (K := K) p)) =
      MvPolynomial.aeval (frameLineVariable (K := K) p) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, aeval_X]
  cases p with
  | none =>
      change MvPolynomial.eval₂ Polynomial.C (fun _ : Unit => Polynomial.X) (X ()) = Polynomial.X
      exact MvPolynomial.eval₂_X _ _ _
  | some j =>
      by_cases h : i = j
      · simp only [frameLineVariableMV, frameLineVariable, h, ↓reduceIte]
        change MvPolynomial.eval₂ Polynomial.C (fun _ : Unit => Polynomial.X) (X ()) = Polynomial.X
        exact MvPolynomial.eval₂_X _ _ _
      · simp only [frameLineVariableMV, frameLineVariable, h, ↓reduceIte, map_zero]

lemma frameProjectivePoint_mem_iff (p : Option (Fin 4)) (f : MvPolynomial (Fin 4) K) :
    f ∈ (frameProjectivePoint (K := K) p).asHomogeneousIdeal ↔
      MvPolynomial.aeval (frameLineVariable (K := K) p) f = 0 := by
  rw [show (frameProjectivePoint (K := K) p).asHomogeneousIdeal = frameLineHomogeneousIdeal p
    from rfl, mem_frameLineHomogeneousIdeal]
  have he := AlgHom.congr_fun (frameLine_eval_comparison (K := K) p) f
  rw [← he]
  exact (map_eq_zero_iff _ (MvPolynomial.uniqueAlgEquiv K Unit).injective).symm

/-- The five explicit quadrics generate the actual projective vanishing ideal
of the displayed five frame points. -/
theorem frame_projective_vanishing_ideal :
    (ProjectiveSpectrum.vanishingIdeal
      (Set.range (frameProjectivePoint (K := K)))).toIdeal = frameIdeal := by
  ext f
  rw [FrameCoordinateRing.mem_frameIdeal_iff]
  constructor
  · intro hf p
    exact (frameProjectivePoint_mem_iff p f).mp
      ((ProjectiveSpectrum.mem_vanishingIdeal _ f).mp hf _ (Set.mem_range_self p))
  · intro hf
    apply (ProjectiveSpectrum.mem_vanishingIdeal _ f).mpr
    rintro _ ⟨p, rfl⟩
    exact (frameProjectivePoint_mem_iff p f).mpr (hf p)

end
end PfaffianDescent
