import PfaffianDescent.LinearNormalizedProjectivePoint
import PfaffianDescent.VoisinRelativeTripleIntersectionFamily

/-!
# Normalized points of a cubic--quadric--quadric intersection

A common zero of the three homogeneous equations, normalized by a linear
form evaluating to one, gives an actual morphism into an affine Proj chart
of their complete intersection. This is the point constructor needed to
turn the eight relative coordinate sections into generic-fiber points.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem tripleIntersectionNormalizedPoint_eval_zero
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (x : Fin 4 → F)
    (hzero : p.eval x = 0 ∧ q.eval x = 0 ∧ r.eval x = 0) :
    ∀ s ∈ (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal,
      s.eval₂ (algebraMap F F) x = 0 := by
  intro s hs
  have hle : (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal ≤
      RingHom.ker (eval₂Hom (algebraMap F F) x) := by
    change Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) F)) ≤ _
    apply Ideal.span_le.mpr
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · simpa using hzero.1
    · simpa using hzero.2.1
    · simpa using hzero.2.2
  exact hle hs

noncomputable def tripleIntersectionNormalizedPointChartMap
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) F)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 4 → F)
    (hzero : p.eval x = 0 ∧ q.eval x = 0 ∧ r.eval x = 0)
    (hnorm : ell.eval x = 1) :
    let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    Away (grading I) (Ideal.Quotient.mk I.toIdeal ell) →+* F := by
  dsimp only
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  have he : ∀ s ∈ I.toIdeal, s.eval₂ (algebraMap F F) x = 0 :=
    tripleIntersectionNormalizedPoint_eval_zero p q r hp hq hr x hzero
  have hn : ell.eval₂ (algebraMap F F) x = 1 := by
    simpa using hnorm
  exact linearNormalizedPointChartMap I x ell hn he

/-- The normalized common zero is an actual field-valued point of the
projective cubic--quadric--quadric scheme. -/
noncomputable def tripleIntersectionNormalizedPoint
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) F)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 4 → F)
    (hzero : p.eval x = 0 ∧ q.eval x = 0 ∧ r.eval x = 0)
    (hnorm : ell.eval x = 1) :
    Spec (.of F) ⟶ scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) :=
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let z := Ideal.Quotient.mk I.toIdeal ell
  let hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  Spec.map (CommRingCat.ofHom
    (tripleIntersectionNormalizedPointChartMap p q r hp hq hr ell hell x hzero hnorm)) ≫
    Proj.awayι (grading I) z hz (by decide : 0 < 1)

theorem tripleIntersectionNormalizedPointChartMap_coordinate
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) F)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 4 → F)
    (hzero : p.eval x = 0 ∧ q.eval x = 0 ∧ r.eval x = 0)
    (hnorm : ell.eval x = 1) (j : Fin 4) :
    let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    tripleIntersectionNormalizedPointChartMap p q r hp hq hr ell hell x hzero hnorm
      (linearChartCoordinate I
        (Ideal.Quotient.mk I.toIdeal ell)
        (polynomial_class_mem_grading I ell hell) j) = x j := by
  dsimp only
  unfold tripleIntersectionNormalizedPointChartMap
  exact linearNormalizedPointChartMap_coordinate
    (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) x ell hell
    (by simpa using hnorm)
    (tripleIntersectionNormalizedPoint_eval_zero p q r hp hq hr x hzero) j

/-- Normalized vectors with distinct coordinates define distinct points of
the projective complete intersection. -/
theorem tripleIntersectionNormalizedPoint_injective
    {F : Type u} [Field F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) F)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → F)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1)
    (hx : Function.Injective x) :
    Function.Injective (fun k => tripleIntersectionNormalizedPoint
      p q r hp hq hr ell hell (x k) (hzero k) (hnorm k)) := by
  intro i j hij
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let z := Ideal.Quotient.mk I.toIdeal ell
  let hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  have hchart :
      Spec.map (CommRingCat.ofHom
        (tripleIntersectionNormalizedPointChartMap
          p q r hp hq hr ell hell (x i) (hzero i) (hnorm i))) =
      Spec.map (CommRingCat.ofHom
        (tripleIntersectionNormalizedPointChartMap
          p q r hp hq hr ell hell (x j) (hzero j) (hnorm j))) := by
    apply (cancel_mono (Proj.awayι (grading I) z hz (by decide : 0 < 1))).mp
    exact hij
  have hmaps : tripleIntersectionNormalizedPointChartMap
        p q r hp hq hr ell hell (x i) (hzero i) (hnorm i) =
      tripleIntersectionNormalizedPointChartMap
        p q r hp hq hr ell hell (x j) (hzero j) (hnorm j) := by
    have h := Spec.map_injective hchart
    exact congrArg CommRingCat.Hom.hom h
  apply hx
  funext l
  have h := congrArg (fun g => g (linearChartCoordinate I z hz l)) hmaps
  have hi := tripleIntersectionNormalizedPointChartMap_coordinate
    p q r hp hq hr ell hell (x i) (hzero i) (hnorm i) l
  have hj := tripleIntersectionNormalizedPointChartMap_coordinate
    p q r hp hq hr ell hell (x j) (hzero j) (hnorm j) l
  exact hi.symm.trans (h.trans hj)

end PfaffianDescent
