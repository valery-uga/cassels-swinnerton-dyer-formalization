import PfaffianDescent.VoisinSimultaneousPolynomialAvoidance
import PfaffianDescent.VoisinGenericFourLineSeparability

/-!
# Simultaneous separability in a polynomial family of cubic lines

This is the parameter-selection layer for a transverse four-line witness on
a fixed cubic.  The geometric input is reduced to proving that the common
leading-coefficient polynomial and each line-discriminant polynomial are
nonzero.  One specialization then makes the parameter determinant nonzero
and every displayed cubic line restriction separable.
-/

namespace PfaffianDescent

open MvPolynomial Polynomial

universe u v w

/-- The restriction of a fixed cubic to a line whose two spanning vectors
have polynomial coordinates. -/
noncomputable def parameterizedCubicLinePolynomial
    {K : Type u} {σ : Type v} [Field K]
    (c : Cubic K 4) (a b : Fin 4 → MvPolynomial σ K) :
    (MvPolynomial σ K)[X] :=
  AllCharacteristics.cubicLinePolynomial (c.map MvPolynomial.C) a b

/-- The line family specializes compatibly after an arbitrary coefficient
field extension. -/
theorem parameterizedCubicLinePolynomial_map_eval₂
    {K : Type u} {L : Type w} {σ : Type v} [Field K] [Field L]
    (f : K →+* L) (c : Cubic K 4)
    (a b : Fin 4 → MvPolynomial σ K) (x : σ → L) :
    (parameterizedCubicLinePolynomial c a b).map
        (MvPolynomial.eval₂Hom f x) =
      AllCharacteristics.cubicLinePolynomial (c.map f)
        (fun j => MvPolynomial.eval₂ f x (a j))
        (fun j => MvPolynomial.eval₂ f x (b j)) := by
  rw [parameterizedCubicLinePolynomial, cubicLinePolynomial_map]
  congr 1
  funext i
  simp [Cubic.map]

/-- Specializing the line parameters specializes the corresponding cubic
line polynomial literally. -/
theorem parameterizedCubicLinePolynomial_map_eval
    {K : Type u} {σ : Type v} [Field K]
    (c : Cubic K 4) (a b : Fin 4 → MvPolynomial σ K)
    (x : σ → K) :
    (parameterizedCubicLinePolynomial c a b).map
        (MvPolynomial.eval₂Hom (RingHom.id K) x) =
      AllCharacteristics.cubicLinePolynomial c
        (fun j => MvPolynomial.eval x (a j))
        (fun j => MvPolynomial.eval x (b j)) := by
  rw [parameterizedCubicLinePolynomial, cubicLinePolynomial_map]
  congr 1
  funext i
  simp [Cubic.map]

/-- Evaluation of the polynomial base-vector coefficient is evaluation of
the original cubic at the specialized base vector. -/
theorem parameterizedCubic_baseEvaluation_eval
    {K : Type u} {σ : Type v} [Field K]
    (c : Cubic K 4) (a : Fin 4 → MvPolynomial σ K)
    (x : σ → K) :
    MvPolynomial.eval x ((c.map MvPolynomial.C).eval a) =
      c.eval (fun j => MvPolynomial.eval x (a j)) := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id K) x
  have h := Cubic.eval_map φ (c.map MvPolynomial.C) a
  have hc : (c.map MvPolynomial.C).map φ = c := by
    funext i
    simp [Cubic.map, φ]
  rw [hc] at h
  exact h.symm

/-- Nonvanishing of the determinant, common leading coefficient, and all
line discriminants can be imposed simultaneously.  At the resulting
parameter, every line restriction is a separable cubic of degree three. -/
theorem exists_parameter_with_det_ne_zero_and_cubicLines_separable
    {K : Type u} {σ : Type v} {ι : Type w}
    [Field K] [CharZero K] [Infinite K]
    [Finite σ] [Fintype ι]
    (c : Cubic K 4) (det : MvPolynomial σ K)
    (a : Fin 4 → MvPolynomial σ K)
    (b : ι → Fin 4 → MvPolynomial σ K)
    (hdet : det ≠ 0)
    (hbase : (c.map MvPolynomial.C).eval a ≠ 0)
    (hdisc : ∀ i, (parameterizedCubicLinePolynomial c a (b i)).discr ≠ 0) :
    ∃ x : σ → K,
      MvPolynomial.eval x det ≠ 0 ∧
      c.eval (fun j => MvPolynomial.eval x (a j)) ≠ 0 ∧
      ∀ i, (AllCharacteristics.cubicLinePolynomial c
        (fun j => MvPolynomial.eval x (a j))
        (fun j => MvPolynomial.eval x (b i j))).Separable := by
  let bad : Option ι → MvPolynomial σ K
    | none => (c.map MvPolynomial.C).eval a
    | some i => (parameterizedCubicLinePolynomial c a (b i)).discr
  have hbad : ∀ i, bad i ≠ 0 := by
    intro i
    cases i with
    | none => exact hbase
    | some i => exact hdisc i
  obtain ⟨x, hdetx, hbadx⟩ :=
    exists_mvPolynomial_eval_det_and_family_ne_zero det bad hdet hbad
  have hbasex : c.eval (fun j => MvPolynomial.eval x (a j)) ≠ 0 := by
    rw [← parameterizedCubic_baseEvaluation_eval c a x]
    exact hbadx none
  refine ⟨x, hdetx, hbasex, ?_⟩
  intro i
  let f := parameterizedCubicLinePolynomial c a (b i)
  let φ := MvPolynomial.eval₂Hom (RingHom.id K) x
  have hf : f.degree = 3 := by
    apply (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr
    exact AllCharacteristics.cubicLinePolynomial_natDegree
      (c.map MvPolynomial.C) a (b i) hbase
  have hmapEq : f.map φ = AllCharacteristics.cubicLinePolynomial c
      (fun j => MvPolynomial.eval x (a j))
      (fun j => MvPolynomial.eval x (b i j)) :=
    parameterizedCubicLinePolynomial_map_eval c a (b i) x
  have hmap : (f.map φ).degree = 3 := by
    apply (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr
    rw [hmapEq]
    exact AllCharacteristics.cubicLinePolynomial_natDegree c _ _ hbasex
  have hdiscMap : (f.map φ).discr ≠ 0 := by
    rw [cubic_discr_map_of_degree_three φ f hf hmap]
    exact hbadx (some i)
  rw [hmapEq] at hdiscMap
  have htargetDegree :
      (AllCharacteristics.cubicLinePolynomial c
        (fun j => MvPolynomial.eval x (a j))
        (fun j => MvPolynomial.eval x (b i j))).degree = 3 := by
    rw [← hmapEq]
    exact hmap
  exact polynomial_separable_of_discr_ne_zero _
    (by rw [htargetDegree]; decide) hdiscMap

end PfaffianDescent
