import PfaffianDescent.VoisinGenericTripleSelectedPoints
import AllCharacteristics.DisjointClosedUnion
import AllCharacteristics.FieldPointClosedLocus

/-! The normalized rational triple-intersection points are closed sections. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem tripleIntersectionNormalizedPoint_toBase
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) F)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 4 → F)
    (hzero : p.eval x = 0 ∧ q.eval x = 0 ∧ r.eval x = 0)
    (hnorm : ell.eval x = 1) :
    tripleIntersectionNormalizedPoint p q r hp hq hr ell hell x hzero hnorm ≫
      toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
        𝟙 (Spec (.of F)) := by
  have he := tripleIntersectionNormalizedPoint_eval_zero p q r hp hq hr x hzero
  have hn : ell.eval₂ (algebraMap F F) x = 1 := by simpa using hnorm
  have hbase := linearNormalizedPoint_toBase
    (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)
    x ell hell hn he
  simpa [tripleIntersectionNormalizedPoint,
    tripleIntersectionNormalizedPointChartMap,
    linearNormalizedPoint] using hbase

theorem tripleIntersectionNormalizedPoint_isClosedImmersion
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) F)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 4 → F)
    (hzero : p.eval x = 0 ∧ q.eval x = 0 ∧ r.eval x = 0)
    (hnorm : ell.eval x = 1) :
    IsClosedImmersion
      (tripleIntersectionNormalizedPoint p q r hp hq hr ell hell x hzero hnorm) := by
  have hcomp : IsClosedImmersion
      (tripleIntersectionNormalizedPoint p q r hp hq hr ell hell x hzero hnorm ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rw [tripleIntersectionNormalizedPoint_toBase]
    infer_instance
  exact IsClosedImmersion.of_comp _
    (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

theorem genericTripleIntersectionSelectedPoints_isClosedImmersion
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
    (k : Fin 8) :
    IsClosedImmersion
      (genericTripleIntersectionSelectedPoints
        p q r hp hq hr ell hell x hzero hnorm k) := by
  let f := algebraMap R (FractionRing R)
  have hz : (p.map f).eval (fun j => f (x k j)) = 0 ∧
      (q.map f).eval (fun j => f (x k j)) = 0 ∧
      (r.map f).eval (fun j => f (x k j)) = 0 := by
    obtain ⟨h₁, h₂, h₃⟩ := hzero k
    simp only [polynomial_eval_map_of_eval, h₁, h₂, h₃, map_zero,
      and_self]
  have hn : (ell.map f).eval (fun j => f (x k j)) = 1 := by
    rw [polynomial_eval_map_of_eval, hnorm k, map_one]
  exact tripleIntersectionNormalizedPoint_isClosedImmersion
    (p.map f) (q.map f) (r.map f)
    (hp.map f) (hq.map f) (hr.map f)
    (ell.map f) (hell.map f) (fun j => f (x k j)) hz hn

theorem genericTripleIntersectionSelectedPoints_toBase
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
    (k : Fin 8) :
    let f := algebraMap R (FractionRing R)
    genericTripleIntersectionSelectedPoints
        p q r hp hq hr ell hell x hzero hnorm k ≫
      toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map f) (q.map f) (r.map f)
        (hp.map f) (hq.map f) (hr.map f)) =
      𝟙 (Spec (.of (FractionRing R))) := by
  dsimp only
  let f := algebraMap R (FractionRing R)
  have hz : (p.map f).eval (fun j => f (x k j)) = 0 ∧
      (q.map f).eval (fun j => f (x k j)) = 0 ∧
      (r.map f).eval (fun j => f (x k j)) = 0 := by
    obtain ⟨h₁, h₂, h₃⟩ := hzero k
    simp only [polynomial_eval_map_of_eval, h₁, h₂, h₃, map_zero,
      and_self]
  have hn : (ell.map f).eval (fun j => f (x k j)) = 1 := by
    rw [polynomial_eval_map_of_eval, hnorm k, map_one]
  exact tripleIntersectionNormalizedPoint_toBase
    (p.map f) (q.map f) (r.map f)
    (hp.map f) (hq.map f) (hr.map f)
    (ell.map f) (hell.map f) (fun j => f (x k j)) hz hn

theorem genericTripleIntersectionSelectedPoints_disjoint_ranges
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
    (hinj : Function.Injective (genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell x hzero hnorm)) :
    Pairwise fun i j : Fin 8 =>
      Disjoint (Set.range (genericTripleIntersectionSelectedPoints
        p q r hp hq hr ell hell x hzero hnorm i))
        (Set.range (genericTripleIntersectionSelectedPoints
          p q r hp hq hr ell hell x hzero hnorm j)) := by
  intro i j hij
  let a := genericTripleIntersectionSelectedPoints
    p q r hp hq hr ell hell x hzero hnorm
  letI : IsClosedImmersion (a j) :=
    genericTripleIntersectionSelectedPoints_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm j
  apply Set.disjoint_iff_forall_ne.mpr
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ hst
  have hs : s = IsLocalRing.closedPoint (FractionRing R) := Subsingleton.elim _ _
  have ht : t = IsLocalRing.closedPoint (FractionRing R) := Subsingleton.elim _ _
  rw [hs, ht] at hst
  have hmem : a i (IsLocalRing.closedPoint (FractionRing R)) ∈ Set.range (a j) :=
    ⟨IsLocalRing.closedPoint (FractionRing R), hst.symm⟩
  obtain ⟨b, hb⟩ :=
    (AllCharacteristics.fieldPoint_mem_closed_range_iff (a j) (a i)).mp hmem
  have hbId : b = 𝟙 (Spec (.of (FractionRing R))) := by
    have h := congrArg (fun c => c ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (algebraMap R (FractionRing R)))
        (q.map (algebraMap R (FractionRing R)))
        (r.map (algebraMap R (FractionRing R)))
        (hp.map (algebraMap R (FractionRing R)))
        (hq.map (algebraMap R (FractionRing R)))
        (hr.map (algebraMap R (FractionRing R))))) hb
    rw [Category.assoc,
      genericTripleIntersectionSelectedPoints_toBase,
      Category.comp_id,
      genericTripleIntersectionSelectedPoints_toBase] at h
    exact h
  rw [hbId, Category.id_comp] at hb
  exact hij (hinj hb.symm)

/-- The eight distinct rational points form an actual closed subscheme of
the finite generic triple intersection. -/
theorem genericTripleIntersectionSelectedPoints_sigmaDesc_isClosedImmersion
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
    (hinj : Function.Injective (genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell x hzero hnorm)) :
    IsClosedImmersion (Sigma.desc
      (genericTripleIntersectionSelectedPoints
        p q r hp hq hr ell hell x hzero hnorm)) := by
  let a := genericTripleIntersectionSelectedPoints
    p q r hp hq hr ell hell x hzero hnorm
  haveI (k : Fin 8) : IsClosedImmersion (a k) :=
    genericTripleIntersectionSelectedPoints_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm k
  exact AllCharacteristics.isClosedImmersion_sigmaDesc_of_disjoint a
    (genericTripleIntersectionSelectedPoints_disjoint_ranges
      p q r hp hq hr ell hell x hzero hnorm hinj)

end PfaffianDescent
