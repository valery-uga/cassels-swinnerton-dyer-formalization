import PfaffianDescent.QuarticTwistedCubicHilbertNinety
import Mathlib.FieldTheory.Galois.NormalBasis

/-!
# Artin independence for the finite-Galois Hilbert--90 calculation

This file puts Mathlib's linear independence of field embeddings in the
coefficient form used by the matrix-averaging proof of Hilbert 90.
-/

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

open scoped BigOperators

universe u v

/-- Distinct automorphisms in a finite Galois group are linearly independent
as functions on the field.  This is the coefficient form needed to show that
Hilbert--90 averages have no common annihilator. -/
lemma gal_artin_independence (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Fintype Gal(L/K)] (c : Gal(L/K) → L)
    (h : ∀ x : L, ∑ σ : Gal(L/K), c σ * σ x = 0) : ∀ σ, c σ = 0 := by
  have hlin : LinearIndependent L
      (fun σ : Gal(L/K) => (σ.toAlgHom : L →ₐ[K] L).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap K L L).comp _ AlgEquiv.coe_toAlgHom_injective
  apply Fintype.linearIndependent_iff.mp hlin c
  apply LinearMap.ext
  intro x
  simpa using h x

end PfaffianDescent.QuarticNet.ProjectiveCocycle

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

universe u v

/-- The action of the Galois group on its field, expressed in the form used by
`LinearCocycle`. -/
noncomputable def galFieldAction (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Gal(L/K) →* L ≃+* L where
  toFun σ := σ.toRingEquiv
  map_one' := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- Artin independence supplies the coefficient hypothesis for the actual
finite-Galois field action. -/
lemma galFieldAction_isArtinIndependent (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Fintype Gal(L/K)] : IsArtinIndependent (galFieldAction K L) := by
  intro c h
  apply gal_artin_independence K L c
  intro x
  simpa [galFieldAction] using h x

end PfaffianDescent.QuarticNet.ProjectiveCocycle

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

universe u v

/-- Matrix Hilbert 90 over a finite Galois extension, in every positive
finite dimension.  The ambient twisted-cubic coordinates use the `n = 4`
instance, while the parameter line uses `n = 2`. -/
theorem LinearCocycle.isCoboundary_of_galois_of_ne_zero
    (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Fintype Gal(L/K)] {n : ℕ}
    (a : LinearCocycle (L := L) (G := Gal(L/K)) n (galFieldAction K L))
    (hn : n ≠ 0) : a.IsCoboundary :=
  a.isCoboundary_of_artin_of_ne_zero (galFieldAction_isArtinIndependent K L) hn

/-- Matrix Hilbert 90 in the binary form needed for twisted-cubic descent. -/
theorem LinearCocycle.isCoboundary_of_galois (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Fintype Gal(L/K)]
    (a : LinearCocycle (L := L) (G := Gal(L/K)) 2 (galFieldAction K L)) : a.IsCoboundary :=
  a.isCoboundary_of_galois_of_ne_zero K L (by omega)

/-- A binary projective cocycle over a finite Galois extension is split when
its symmetric cube is split. -/
theorem isCoboundary_of_symmetricCube_isCoboundary_galois
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)]
    (c : ProjectiveCocycle (L := L) 2 (galFieldAction K L))
    (hc : (symmetricCube c).IsCoboundary) : c.IsCoboundary := by
  let l := chooseLift c
  obtain ⟨u, hu⟩ := l.defect_isCoboundary_of_symmetricCube_isCoboundary c hc
  exact l.projective_isCoboundary_of_strictify_isCoboundary c u hu
    ((l.strictify c u hu).isCoboundary_of_galois K L)


end PfaffianDescent.QuarticNet.ProjectiveCocycle
