import PfaffianDescent.CorayOriginalFiniteEtaleCoefficientKernel
import Mathlib.Data.Fintype.EquivFin

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct
universe u
set_option autoImplicit false

/-- Actual degree3 of the SAME original finite etale algebra constructs
an enumeration of ALL its geometric points with any actual first point
placed at index0. No supplied cardinality, embeddings or conjugate list. -/
theorem originalFiniteEtale_degreeThree_exists_geometricEnumeration_at_actualPoint001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    (hRank : Module.finrank K A = 3) (p0 : PrimeSpectrum (M ⊗[K] A)) :
    ∃ e : Fin 3 ≃ PrimeSpectrum (M ⊗[K] A), e 0 = p0 := by
  classical
  let D := M ⊗[K] A
  letI : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  letI : Module.Finite M D := inferInstance
  letI : IsArtinianRing D := isArtinian_of_tower M inferInstance
  letI : Fintype (PrimeSpectrum D) := Fintype.ofFinite _
  have hCard : Fintype.card (PrimeSpectrum D) = 3 := by
    have h := (originalFiniteEtaleGeometricPoints_natCard_eq_originalFinrank001
      (K := K) (A := A) (M := M)).trans hRank
    simpa only [Nat.card_eq_fintype_card] using h
  let E : PrimeSpectrum D ≃ Fin 3 := Fintype.equivFinOfCardEq hCard
  let e : Fin 3 ≃ PrimeSpectrum D := (Equiv.swap (0 : Fin 3) (E p0)).trans E.symm
  refine ⟨e, ?_⟩
  change E.symm (Equiv.swap (0 : Fin 3) (E p0) 0) = p0
  rw [Equiv.swap_apply_left, E.symm_apply_apply]

/-- The three actual enumerated evaluations are EXACTLY all geometric
row conditions on the SAME scalar-extended algebra. No kernel equality
or replacement of the original degree3 point by three unrelated points. -/
theorem originalFiniteEtale_geometricCoefficientKernel_threeActualRows_iff001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    (e : Fin 3 ≃ PrimeSpectrum (M ⊗[K] A)) {m : ℕ}
    (v : Fin m → A) (c : Fin m → M) :
    originalFiniteEtaleGeometricCoefficientEvaluation (K := K) (M := M) v c = 0 ↔
      (∑ i, c i * originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) (e 0) (v i)) = 0 ∧
      (∑ i, c i * originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) (e 1) (v i)) = 0 ∧
      (∑ i, c i * originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) (e 2) (v i)) = 0 := by
  constructor
  · intro h
    exact ⟨by simpa only [originalFiniteEtaleGeometricCoefficientEvaluation_apply001, Pi.zero_apply] using congrFun h (e 0),
      by simpa only [originalFiniteEtaleGeometricCoefficientEvaluation_apply001, Pi.zero_apply] using congrFun h (e 1),
      by simpa only [originalFiniteEtaleGeometricCoefficientEvaluation_apply001, Pi.zero_apply] using congrFun h (e 2)⟩
  · rintro ⟨h0, h1, h2⟩
    funext p
    obtain ⟨i, rfl⟩ := e.surjective p
    fin_cases i
    · simp only [originalFiniteEtaleGeometricCoefficientEvaluation_apply001, Pi.zero_apply]
      change (∑ i, c i * originalFiniteEtaleGeometricPoint
        (K := K) (A := A) (M := M) (e (0 : Fin 3)) (v i)) = 0
      exact h0
    · simp only [originalFiniteEtaleGeometricCoefficientEvaluation_apply001, Pi.zero_apply]
      change (∑ i, c i * originalFiniteEtaleGeometricPoint
        (K := K) (A := A) (M := M) (e (1 : Fin 3)) (v i)) = 0
      exact h1
    · simp only [originalFiniteEtaleGeometricCoefficientEvaluation_apply001, Pi.zero_apply]
      change (∑ i, c i * originalFiniteEtaleGeometricPoint
        (K := K) (A := A) (M := M) (e (2 : Fin 3)) (v i)) = 0
      exact h2

end PfaffianDescent.Coray
