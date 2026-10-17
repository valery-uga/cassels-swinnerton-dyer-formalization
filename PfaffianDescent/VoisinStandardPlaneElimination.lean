import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Algebra.MvPolynomial.Equiv
import PfaffianDescent.VoisinConicRegularLinearCoordinate

/-!
# Eliminating the standard plane equation

The quotient of the four-variable homogeneous coordinate ring by the first
coordinate is the three-variable polynomial ring. This is the coordinate
normalization needed to transfer the conic saturation lemma to a plane in
projective three-space.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

noncomputable def standardPlaneQuotientEquiv
    {K : Type u} [Field K] :
    (MvPolynomial (Fin 4) K ⧸
      Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K))) ≃ₐ[K]
        MvPolynomial (Fin 3) K := by
  let e := MvPolynomial.finSuccEquiv K 3
  have hI : Ideal.span ({Polynomial.X} :
        Set (Polynomial (MvPolynomial (Fin 3) K))) =
      (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K))).map e.toRingHom := by
    rw [Ideal.map_span]
    simp [e, MvPolynomial.finSuccEquiv_X_zero]
  exact (Ideal.quotientEquivAlg
    (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)))
    (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 3) K))))
    e hI).trans
      ((Ideal.quotientEquivAlgOfEq K (by simp)).trans
        ((Polynomial.quotientSpanXSubCAlgEquiv
          (0 : MvPolynomial (Fin 3) K)).restrictScalars K))

theorem standardPlaneQuotientEquiv_mk
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) :
    standardPlaneQuotientEquiv
        (Ideal.Quotient.mk
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K))) p) =
      (MvPolynomial.finSuccEquiv K 3 p).eval 0 := by
  rfl

@[simp] theorem standardPlaneQuotientEquiv_X_zero
    {K : Type u} [Field K] :
    standardPlaneQuotientEquiv (K := K)
        (Ideal.Quotient.mk
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)))
          (X 0 : MvPolynomial (Fin 4) K)) = 0 := by
  rw [standardPlaneQuotientEquiv_mk, MvPolynomial.finSuccEquiv_X_zero]
  simp

@[simp] theorem standardPlaneQuotientEquiv_X_succ
    {K : Type u} [Field K] (j : Fin 3) :
    standardPlaneQuotientEquiv (K := K)
        (Ideal.Quotient.mk
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)))
          (X j.succ : MvPolynomial (Fin 4) K)) = X j := by
  rw [standardPlaneQuotientEquiv_mk, MvPolynomial.finSuccEquiv_X_succ]
  simp

/-- Substitution of zero for the eliminated coordinate. -/
noncomputable def standardPlaneEval
    {K : Type u} [Field K] :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval (Fin.cases 0 X)

@[simp] theorem standardPlaneEval_X_zero
    {K : Type u} [Field K] :
    standardPlaneEval (K := K) (X 0 : MvPolynomial (Fin 4) K) = 0 := by
  simp [standardPlaneEval]

@[simp] theorem standardPlaneEval_X_succ
    {K : Type u} [Field K] (j : Fin 3) :
    standardPlaneEval (K := K) (X j.succ : MvPolynomial (Fin 4) K) = X j := by
  simp [standardPlaneEval]

theorem standardPlaneEval_homogeneous
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    (standardPlaneEval p).IsHomogeneous d := by
  have hX (i : Fin 4) :
      (Fin.cases (motive := fun _ : Fin 4 => MvPolynomial (Fin 3) K)
        (0 : MvPolynomial (Fin 3) K)
        (fun j : Fin 3 => (X j : MvPolynomial (Fin 3) K)) i).IsHomogeneous 1 := by
    cases i using Fin.cases with
    | zero => exact (homogeneousSubmodule (Fin 3) K 1).zero_mem
    | succ j => exact isHomogeneous_X K j
  change (MvPolynomial.aeval (Fin.cases 0 X) p).IsHomogeneous d
  simpa only [one_mul] using hp.aeval _ hX

theorem standardPlaneEval_eq_quotient
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) :
    standardPlaneEval p =
      standardPlaneQuotientEquiv
        (Ideal.Quotient.mk
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K))) p) := by
  have h : standardPlaneEval (K := K) =
      (standardPlaneQuotientEquiv (K := K)).toAlgHom.comp
        (Ideal.Quotient.mkₐ K
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ j => simp
  exact DFunLike.congr_fun h p

/-- Elimination also commutes with imposing the quadratic equation of a
plane conic. No reducedness or irreducibility is required. -/
noncomputable def standardPlaneConicQuotientEquiv
    {K : Type u} [Field K] (q : MvPolynomial (Fin 4) K) :
    (MvPolynomial (Fin 4) K ⧸
      (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
        Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))) ≃ₐ[K]
      (MvPolynomial (Fin 3) K ⧸
        Ideal.span ({standardPlaneEval q} : Set (MvPolynomial (Fin 3) K))) := by
  let I : Ideal (MvPolynomial (Fin 4) K) := Ideal.span ({X 0} : Set _)
  let J : Ideal (MvPolynomial (Fin 4) K) := Ideal.span ({q} : Set _)
  let E := standardPlaneQuotientEquiv (K := K)
  have hJ : Ideal.span ({standardPlaneEval q} : Set (MvPolynomial (Fin 3) K)) =
      (J.map (Ideal.Quotient.mkₐ K I)).map E.toRingHom := by
    simp [J, I, Ideal.map_span, standardPlaneEval_eq_quotient, E]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ K I J).symm.trans
    (Ideal.quotientEquivAlg
      (J.map (Ideal.Quotient.mkₐ K I))
      (Ideal.span ({standardPlaneEval q} : Set (MvPolynomial (Fin 3) K))) E hJ)

@[simp] theorem standardPlaneConicQuotientEquiv_X_succ
    {K : Type u} [Field K] (q : MvPolynomial (Fin 4) K) (j : Fin 3) :
    standardPlaneConicQuotientEquiv q
      (Ideal.Quotient.mk
        (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))
        (X j.succ : MvPolynomial (Fin 4) K)) =
      Ideal.Quotient.mk
        (Ideal.span ({standardPlaneEval q} : Set (MvPolynomial (Fin 3) K)))
        (X j : MvPolynomial (Fin 3) K) := by
  simp only [standardPlaneConicQuotientEquiv, AlgEquiv.trans_apply,
    DoubleQuot.coe_quotQuotEquivQuotSupₐ_symm,
    DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk]
  change Ideal.Quotient.mk _
      (standardPlaneQuotientEquiv
        (Ideal.Quotient.mk
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)))
          (X j.succ : MvPolynomial (Fin 4) K))) = _
  rw [standardPlaneQuotientEquiv_X_succ]

/-- For a conic in the standard plane `X₀ = 0`, some other projective
coordinate acts injectively on the full four-variable quotient. The
quadratic may restrict to zero, factor, or be a square. -/
theorem exists_regular_coordinate_mod_standard_plane_conic
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2) :
    ∃ j : Fin 3, Function.Injective
      (fun x : MvPolynomial (Fin 4) K ⧸
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))) =>
        Ideal.Quotient.mk
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))
          (X j.succ : MvPolynomial (Fin 4) K) * x) := by
  let E := standardPlaneConicQuotientEquiv q
  let I₃ : Ideal (MvPolynomial (Fin 3) K) :=
    Ideal.span ({standardPlaneEval q} : Set _)
  obtain ⟨j, hj⟩ := exists_regular_coordinate_mod_homogeneous_quadratic_any
    (standardPlaneEval q) (standardPlaneEval_homogeneous hq)
  have hreg : Ideal.Quotient.mk I₃ (X j : MvPolynomial (Fin 3) K) ∈
      nonZeroDivisors (MvPolynomial (Fin 3) K ⧸ I₃) :=
    quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal I₃ (X j) hj
  refine ⟨j, ?_⟩
  intro x y hxy
  apply E.injective
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff.mp hreg).1
  rw [mul_sub, sub_eq_zero]
  change (Ideal.Quotient.mk I₃ (X j) : MvPolynomial (Fin 3) K ⧸ I₃) * E x =
    Ideal.Quotient.mk I₃ (X j) * E y
  rw [← standardPlaneConicQuotientEquiv_X_succ q j]
  simpa only [map_mul] using congrArg E hxy

/-- The homogeneous ideal `(X₀,q)` has no irrelevant socle. This is the
exact algebraic saturation condition for a plane conic in standard
coordinates. -/
theorem standard_plane_conic_no_irrelevant_annihilator
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2) :
    ∀ x : MvPolynomial (Fin 4) K ⧸
        (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))),
      (∀ i : Fin 4,
        Ideal.Quotient.mk
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))
          (X i : MvPolynomial (Fin 4) K) * x = 0) → x = 0 := by
  obtain ⟨j, hj⟩ := exists_regular_coordinate_mod_standard_plane_conic q hq
  intro x hx
  apply hj
  simpa only [mul_zero] using hx j.succ

/-- The standard plane-conic ideal is saturated with respect to the four
standard projective charts: a polynomial whose class vanishes in each
coordinate localization already lies in `(X₀,q)`. -/
theorem mem_standard_plane_conic_ideal_of_all_coordinate_localizations_zero
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) K)
    (hzero : ∀ i : Fin 4,
      algebraMap
        (MvPolynomial (Fin 4) K ⧸
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))))
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk
            (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
              Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))
            (X i : MvPolynomial (Fin 4) K))))
        (Ideal.Quotient.mk
          (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))) F) = 0) :
    F ∈ (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
      Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))) := by
  obtain ⟨j, hj⟩ := exists_regular_coordinate_mod_standard_plane_conic q hq
  exact mem_of_localization_eq_zero_of_quotient_mul_injective
    _ (X j.succ) F hj (hzero j.succ)

end PfaffianDescent
