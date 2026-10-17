import PfaffianDescent.VoisinStandardPlaneElimination
import PfaffianDescent.PolynomialLinearChange

/-!
# Transporting plane-conic saturation through a linear coordinate change

The standard-plane computation applies after any invertible linear change
of the four ambient coordinates. This file transports its regular linear
form through the induced equivalence of coordinate rings.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

/-- A linear coordinate change sends each variable into the irrelevant
coordinate ideal. -/
theorem linearCoordinate_mem_coordinate_ideal
    {K : Type u} [Field K]
    (M : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    linearCoordinate M i ∈
      Ideal.span (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K)) := by
  change (∑ j : Fin 4, C (M i j) * X j) ∈
    Ideal.span (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K))
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- If all projective coordinates annihilate a quotient element, then so
does every linear form in their ideal. -/
theorem quotient_mul_zero_of_all_coordinates_mul_zero
    {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin 4) K))
    (s : MvPolynomial (Fin 4) K)
    (hs : s ∈ Ideal.span
      (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K)))
    (x : MvPolynomial (Fin 4) K ⧸ I)
    (hx : ∀ i : Fin 4, Ideal.Quotient.mk I
      (X i : MvPolynomial (Fin 4) K) * x = 0) :
    Ideal.Quotient.mk I s * x = 0 := by
  let N : Submodule (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K ⧸ I) := Submodule.span _ {x}
  have hle : Ideal.span
      (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K)) ≤ N.annihilator := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (Submodule.mem_annihilator_span_singleton x (X i)).mpr
    change Ideal.Quotient.mk I (X i) * x = 0
    exact hx i
  have h := (Submodule.mem_annihilator_span_singleton x s).mp (hle hs)
  change Ideal.Quotient.mk I s * x = 0 at h
  exact h

noncomputable def transformedPlaneConicQuotientEquiv
    {K : Type u} [Field K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (q : MvPolynomial (Fin 4) K) :
    (MvPolynomial (Fin 4) K ⧸
      (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
        Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))) ≃ₐ[K]
      (MvPolynomial (Fin 4) K ⧸
        (Ideal.span ({linearSubstitutionEquiv M hM (X 0)} :
          Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({linearSubstitutionEquiv M hM q} :
            Set (MvPolynomial (Fin 4) K)))) := by
  let E := linearSubstitutionEquiv M hM
  have hI :
      (Ideal.span ({E (X 0)} : Set (MvPolynomial (Fin 4) K)) ⊔
        Ideal.span ({E q} : Set (MvPolynomial (Fin 4) K))) =
      (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
        Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))).map E.toRingHom := by
    simp [Ideal.map_sup, Ideal.map_span]
  exact Ideal.quotientEquivAlg _ _ E hI

@[simp] theorem transformedPlaneConicQuotientEquiv_mk
    {K : Type u} [Field K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (q p : MvPolynomial (Fin 4) K) :
    transformedPlaneConicQuotientEquiv M hM q
      (Ideal.Quotient.mk
        (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))) p) =
      Ideal.Quotient.mk
        (Ideal.span ({linearSubstitutionEquiv M hM (X 0)} :
          Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({linearSubstitutionEquiv M hM q} :
            Set (MvPolynomial (Fin 4) K)))
        (linearSubstitutionEquiv M hM p) := by
  rfl

/-- Every linearly transformed standard plane conic has a regular
homogeneous linear form in its coordinate ring, even when the conic is
reducible or nonreduced. -/
theorem exists_regular_linear_form_mod_transformed_plane_conic
    {K : Type u} [Field K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2) :
    ∃ s : MvPolynomial (Fin 4) K,
      s.IsHomogeneous 1 ∧
      s ∈ Ideal.span
        (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K)) ∧
      Function.Injective
        (fun x : MvPolynomial (Fin 4) K ⧸
            (Ideal.span ({linearSubstitutionEquiv M hM (X 0)} :
              Set (MvPolynomial (Fin 4) K)) ⊔
              Ideal.span ({linearSubstitutionEquiv M hM q} :
                Set (MvPolynomial (Fin 4) K))) =>
          Ideal.Quotient.mk
            (Ideal.span ({linearSubstitutionEquiv M hM (X 0)} :
              Set (MvPolynomial (Fin 4) K)) ⊔
              Ideal.span ({linearSubstitutionEquiv M hM q} :
                Set (MvPolynomial (Fin 4) K))) s * x) := by
  let P := linearSubstitutionEquiv M hM
  let E := transformedPlaneConicQuotientEquiv M hM q
  obtain ⟨j, hj⟩ := exists_regular_coordinate_mod_standard_plane_conic q hq
  refine ⟨P (X j.succ), linearSubstitution_homogeneous M
    (isHomogeneous_X K j.succ), ?_, ?_⟩
  · simpa [P, linearSubstitutionEquiv, linearSubstitution_X] using
      linearCoordinate_mem_coordinate_ideal M j.succ
  intro x y hxy
  apply E.symm.injective
  apply hj
  have hs : E.symm
      (Ideal.Quotient.mk
        (Ideal.span ({P (X 0)} : Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({P q} : Set (MvPolynomial (Fin 4) K)))
        (P (X j.succ))) =
      Ideal.Quotient.mk
        (Ideal.span ({X 0} : Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))
        (X j.succ) := by
    apply E.injective
    simp [E, P]
  have h := congrArg E.symm hxy
  simp only [map_mul] at h
  rw [hs] at h
  exact h

/-- Saturation survives every invertible linear coordinate change. The
regular element need not itself be one of the original coordinates; its
membership in their ideal is enough to kill any irrelevant socle. -/
theorem transformed_plane_conic_no_irrelevant_annihilator
    {K : Type u} [Field K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2) :
    ∀ x : MvPolynomial (Fin 4) K ⧸
        (Ideal.span ({linearSubstitutionEquiv M hM (X 0)} :
          Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({linearSubstitutionEquiv M hM q} :
            Set (MvPolynomial (Fin 4) K))),
      (∀ i : Fin 4,
        Ideal.Quotient.mk
          (Ideal.span ({linearSubstitutionEquiv M hM (X 0)} :
            Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({linearSubstitutionEquiv M hM q} :
              Set (MvPolynomial (Fin 4) K)))
          (X i : MvPolynomial (Fin 4) K) * x = 0) → x = 0 := by
  obtain ⟨s, -, hs, hinj⟩ :=
    exists_regular_linear_form_mod_transformed_plane_conic M hM q hq
  intro x hx
  apply hinj
  simpa only [mul_zero] using
    quotient_mul_zero_of_all_coordinates_mul_zero _ s hs x hx

end PfaffianDescent
