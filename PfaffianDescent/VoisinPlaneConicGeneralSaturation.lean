import PfaffianDescent.VoisinPlaneLinearNormalization
import PfaffianDescent.VoisinPlaneConicLinearChangeSaturation
import PfaffianDescent.ProjectiveIdealSaturation

/-!
# Saturation of arbitrary plane-conic ideals

An arbitrary nonzero homogeneous plane equation can be made the first
coordinate by an invertible linear change. The standard-plane regular-form
argument therefore applies to its intersection with any homogeneous quadric.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

theorem plane_conic_pair_ideal_eq_sup
    {K : Type u} [Field K]
    (ell q : MvPolynomial (Fin 4) K) :
    Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)) =
      Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
        Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)) := by
  rw [← Ideal.span_union]
  congr 1

/-- The coordinate ring of any plane conic has no element annihilated by
all four ambient projective coordinates. No smoothness or reducedness is
required of the conic. -/
theorem plane_conic_no_irrelevant_annihilator
    {K : Type u} [Field K]
    (ell q : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2) :
    ∀ x : MvPolynomial (Fin 4) K ⧸
        (Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
          Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))),
      (∀ i : Fin 4,
        Ideal.Quotient.mk
          (Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))
          (X i : MvPolynomial (Fin 4) K) * x = 0) → x = 0 := by
  obtain ⟨M, hM, he⟩ :=
    exists_linear_change_for_plane_equation ell hell hell0
  let E := linearSubstitutionEquiv M hM
  let q₀ := E.symm q
  have hq₀ : q₀.IsHomogeneous 2 := by
    change (linearSubstitution M⁻¹ q).IsHomogeneous 2
    exact linearSubstitution_homogeneous M⁻¹ hq
  have hqeq : E q₀ = q := E.apply_symm_apply q
  rw [he, ← hqeq]
  exact transformed_plane_conic_no_irrelevant_annihilator M hM q₀ hq₀

/-- A polynomial vanishing in all four coordinate localizations of an
arbitrary plane-conic quotient already lies in its defining ideal. -/
theorem mem_plane_conic_ideal_of_all_coordinate_localizations_zero
    {K : Type u} [Field K]
    (ell q F : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2)
    (hzero : ∀ i : Fin 4,
      algebraMap
        (MvPolynomial (Fin 4) K ⧸
          (Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))))
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk
            (Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
              Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))
            (X i))))
        (Ideal.Quotient.mk
          (Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))) F) = 0) :
    F ∈ Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
      Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)) := by
  let I : Ideal (MvPolynomial (Fin 4) K) :=
    Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
      Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))
  apply mem_of_coordinate_localization_eq_zero_of_no_irrelevant_annihilator
    I (X 0) (X 1) (X 2) (X 3) F ?_ ?_
  · intro x h0 h1 h2 h3
    apply plane_conic_no_irrelevant_annihilator ell q hell hell0 hq x
    intro i
    fin_cases i <;> assumption
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hzero 0
    · exact hzero 1
    · exact hzero 2
    · exact hzero 3

/-- The quotient-ring form of coordinate-chart faithfulness. -/
theorem plane_conic_quotient_eq_zero_of_all_coordinate_localizations_zero
    {K : Type u} [Field K]
    (ell q : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2)
    (x : MvPolynomial (Fin 4) K ⧸
      (Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
        Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))))
    (hx : ∀ i : Fin 4,
      algebraMap
        (MvPolynomial (Fin 4) K ⧸
          (Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
            Ideal.span ({q} : Set (MvPolynomial (Fin 4) K))))
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk
            (Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
              Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)))
            (X i)))) x = 0) : x = 0 := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr
    (mem_plane_conic_ideal_of_all_coordinate_localizations_zero
      ell q F hell hell0 hq hx)

/-- The same quotient criterion in the two-generator ideal notation used by
the projective conic construction. -/
theorem plane_conic_pair_quotient_eq_zero_of_all_coordinate_localizations_zero
    {K : Type u} [Field K]
    (ell q : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2)
    (x : MvPolynomial (Fin 4) K ⧸
      Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)))
    (hx : ∀ i : Fin 4,
      algebraMap
        (MvPolynomial (Fin 4) K ⧸
          Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)))
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk
            (Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)))
            (X i)))) x = 0) : x = 0 := by
  let I : Ideal (MvPolynomial (Fin 4) K) :=
    Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))
  have hsocle : ∀ y : MvPolynomial (Fin 4) K ⧸ I,
      (∀ i : Fin 4, Ideal.Quotient.mk I (X i) * y = 0) → y = 0 := by
    rw [show I = Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) ⊔
      Ideal.span ({q} : Set (MvPolynomial (Fin 4) K)) from
      plane_conic_pair_ideal_eq_sup ell q]
    exact plane_conic_no_irrelevant_annihilator ell q hell hell0 hq
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  apply mem_of_coordinate_localization_eq_zero_of_no_irrelevant_annihilator
    I (X 0) (X 1) (X 2) (X 3) F ?_ ?_
  · intro y h0 h1 h2 h3
    apply hsocle y
    intro i
    fin_cases i <;> assumption
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hx 0
    · exact hx 1
    · exact hx 2
    · exact hx 3

end PfaffianDescent
