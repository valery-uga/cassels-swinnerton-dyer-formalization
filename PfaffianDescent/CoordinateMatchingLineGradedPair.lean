import PfaffianDescent.MatchingCoordinateLineSchemes
import PfaffianDescent.GradedSurjection
import Mathlib.Algebra.MvPolynomial.Rename

/-! SOURCE ONLY, UNVERIFIED. An actual graded inverse pair between the
coordinate line quotient and the TWO-variable polynomial ring. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable (E : Type u) [Field E]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "J" => coordinateMatchingLineIdeal (K := E) false
local notation "PS₂" => homogeneousSubmodule (Fin 2) E

def coordinateMatchingLineGradedRestriction : grading J →+*ᵍ PS₂ where
  __ := Ideal.Quotient.lift (J).toIdeal (coordinateLineRestriction (K := E)).toRingHom
    (fun q hq => (coordinateMatchingLineRestriction_zero_iff_mem false q).mpr hq)
  map_mem := by
    intro n x hx
    obtain ⟨q, hq, rfl⟩ := hx
    change (coordinateLineRestriction q).IsHomogeneous n
    exact coordinateLineRestriction_homogeneous hq

def coordinateMatchingLineGradedInclusion : PS₂ →+*ᵍ grading J where
  __ := (Ideal.Quotient.mk (J).toIdeal).comp
    (MvPolynomial.rename (Fin.castAdd 2 : Fin 2 → Fin 4)).toRingHom
  map_mem := by
    intro n q hq
    exact ⟨MvPolynomial.rename (Fin.castAdd 2 : Fin 2 → Fin 4) q,
      hq.rename_isHomogeneous, rfl⟩

@[simp] theorem coordinateMatchingLineGradedRestriction_mk
    (q : MvPolynomial (Fin 4) E) :
    coordinateMatchingLineGradedRestriction E (Ideal.Quotient.mk (J).toIdeal q) =
      coordinateLineRestriction q := rfl

@[simp] theorem coordinateMatchingLineGradedInclusion_apply
    (q : MvPolynomial (Fin 2) E) :
    coordinateMatchingLineGradedInclusion E q = Ideal.Quotient.mk (J).toIdeal
      (MvPolynomial.rename (Fin.castAdd 2 : Fin 2 → Fin 4) q) := rfl

theorem coordinateMatchingLineGradedRestriction_comp_inclusion :
    (coordinateMatchingLineGradedRestriction E).comp
      (coordinateMatchingLineGradedInclusion E) = GradedRingHom.id PS₂ := by
  have h : (coordinateLineRestriction (K := E)).comp
      (MvPolynomial.rename (Fin.castAdd 2 : Fin 2 → Fin 4)) =
      AlgHom.id E (MvPolynomial (Fin 2) E) := by
    ext i : 1
    fin_cases i <;> simp [coordinateLineRestriction]
  apply GradedRingHom.ext
  intro q
  change coordinateMatchingLineGradedRestriction E
    (coordinateMatchingLineGradedInclusion E q) = q
  rw [coordinateMatchingLineGradedInclusion_apply,
    coordinateMatchingLineGradedRestriction_mk]
  exact AlgHom.congr_fun h q

theorem coordinateMatchingLineGradedInclusion_comp_restriction :
    (coordinateMatchingLineGradedInclusion E).comp
      (coordinateMatchingLineGradedRestriction E) = GradedRingHom.id (grading J) := by
  let mk := Ideal.Quotient.mkₐ E (J).toIdeal
  have hkill (i : Fin 4) (hi : X i ∈ (J).toIdeal) : mk (X i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have h2 : mk (X 2) = 0 := by
    apply hkill
    change X 2 ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))
    exact Ideal.subset_span (by simp)
  have h3 : mk (X 3) = 0 := by
    apply hkill
    change X 3 ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))
    exact Ideal.subset_span (by simp)
  have h : (mk.comp (MvPolynomial.rename (Fin.castAdd 2 : Fin 2 → Fin 4))).comp
      (coordinateLineRestriction (K := E)) = mk := by
    ext i : 1
    fin_cases i <;> simp [coordinateLineRestriction, AlgHom.comp_apply, h2, h3]
  apply GradedRingHom.ext
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change coordinateMatchingLineGradedInclusion E
    (coordinateMatchingLineGradedRestriction E (Ideal.Quotient.mk (J).toIdeal q)) =
    Ideal.Quotient.mk (J).toIdeal q
  rw [coordinateMatchingLineGradedRestriction_mk,
    coordinateMatchingLineGradedInclusion_apply]
  exact AlgHom.congr_fun h q

theorem coordinateMatchingLineGradedRestriction_surjective :
    Function.Surjective (coordinateMatchingLineGradedRestriction E) := by
  intro q
  refine ⟨coordinateMatchingLineGradedInclusion E q, ?_⟩
  exact DFunLike.congr_fun (coordinateMatchingLineGradedRestriction_comp_inclusion E) q

theorem coordinateMatchingLineGradedInclusion_surjective :
    Function.Surjective (coordinateMatchingLineGradedInclusion E) := by
  intro x
  refine ⟨coordinateMatchingLineGradedRestriction E x, ?_⟩
  exact DFunLike.congr_fun (coordinateMatchingLineGradedInclusion_comp_restriction E) x

end PfaffianDescent.QuarticNet
