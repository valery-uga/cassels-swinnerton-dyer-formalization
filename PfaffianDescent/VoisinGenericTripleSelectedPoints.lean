import PfaffianDescent.VoisinTripleIntersectionNormalizedPoints

/-!
# Generic-fiber points from normalized relative sections

Equation-level vanishing and linear-form normalization survive passage to
the fraction field. Each selected relative coordinate section therefore
defines an actual point of the projective generic triple intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomial_eval_map_of_eval
    {R : Type u} [CommRing R]
    {F : Type u} [CommRing F]
    (f : R →+* F)
    (p : MvPolynomial (Fin 4) R)
    (x : Fin 4 → R) :
    (p.map f).eval (fun j => f (x j)) = f (p.eval x) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp f x p).symm

noncomputable def genericTripleIntersectionSelectedPoints
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1) :
    let f := algebraMap R (FractionRing R)
    Fin 8 → (Spec (.of (FractionRing R)) ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal
        (p.map f) (q.map f) (r.map f)
        (hp.map f) (hq.map f) (hr.map f))) := by
  dsimp only
  let f := algebraMap R (FractionRing R)
  intro k
  have hz : (p.map f).eval (fun j => f (x k j)) = 0 ∧
      (q.map f).eval (fun j => f (x k j)) = 0 ∧
      (r.map f).eval (fun j => f (x k j)) = 0 := by
    obtain ⟨h₁, h₂, h₃⟩ := hzero k
    simp only [polynomial_eval_map_of_eval, h₁, h₂, h₃, map_zero,
      and_self]
  have hn : (ell.map f).eval (fun j => f (x k j)) = 1 := by
    rw [polynomial_eval_map_of_eval, hnorm k, map_one]
  exact tripleIntersectionNormalizedPoint
    (p.map f) (q.map f) (r.map f)
    (hp.map f) (hq.map f) (hr.map f)
    (ell.map f) (hell.map f)
    (fun j => f (x k j)) hz hn

theorem genericTripleIntersectionSelectedPoints_injective
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1)
    (hx : Function.Injective x) :
    Function.Injective (genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell x hzero hnorm) := by
  let f := algebraMap R (FractionRing R)
  have hxF : Function.Injective (fun k j => f (x k j)) := by
    intro i j hij
    apply hx
    funext l
    exact IsFractionRing.injective R (FractionRing R) (congrFun hij l)
  have hzF (k : Fin 8) :
      (p.map f).eval (fun j => f (x k j)) = 0 ∧
      (q.map f).eval (fun j => f (x k j)) = 0 ∧
      (r.map f).eval (fun j => f (x k j)) = 0 := by
    obtain ⟨h₁, h₂, h₃⟩ := hzero k
    simp only [polynomial_eval_map_of_eval, h₁, h₂, h₃, map_zero,
      and_self]
  have hnF (k : Fin 8) :
      (ell.map f).eval (fun j => f (x k j)) = 1 := by
    rw [polynomial_eval_map_of_eval, hnorm k, map_one]
  exact tripleIntersectionNormalizedPoint_injective
    (p.map f) (q.map f) (r.map f)
    (hp.map f) (hq.map f) (hr.map f)
    (ell.map f) (hell.map f)
    (fun k j => f (x k j)) hzF hnF hxF

/-- The actual relative equations admit eight distinct, explicitly
constructed generic-fiber projective points from the chosen sections. -/
def HasEightDistinctGenericTriplePoints
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R) : Prop :=
  ∃ (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1),
    Function.Injective (genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell x hzero hnorm)

theorem hasEightDistinctGenericTriplePoints_of_equations
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1)
    (hx : Function.Injective x) :
    HasEightDistinctGenericTriplePoints p q r hp hq hr ell hell x := by
  exact ⟨hzero, hnorm,
    genericTripleIntersectionSelectedPoints_injective
      p q r hp hq hr ell hell x hzero hnorm hx⟩

/-- Permuting the labels preserves the actual eight distinct generic
intersection points. -/
theorem hasEightDistinctGenericTriplePoints_relabel
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (σ : Equiv.Perm (Fin 8))
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x) :
    HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell (fun k => x (σ k)) := by
  obtain ⟨hzero, hnorm, hinj⟩ := hEight
  let hzero' (k : Fin 8) := hzero (σ k)
  let hnorm' (k : Fin 8) := hnorm (σ k)
  refine ⟨hzero', hnorm', ?_⟩
  intro i j hij
  apply σ.injective
  apply hinj
  exact hij

end PfaffianDescent
