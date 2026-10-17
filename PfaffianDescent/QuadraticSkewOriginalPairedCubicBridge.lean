import PfaffianDescent.QuadraticSkewConjugateProjectorFrame
import PfaffianDescent.QuadraticSkewMixedBlockNormalForm
import PfaffianDescent.BasisMatchingProjectorWholeUnionIdeal
import PfaffianDescent.PolynomialLinearChange
import Mathlib.Tactic
/-! SOURCE ONLY / UNVERIFIED. Coordinate and exchange identities below
are derived from actual exchanged lines in the original cubic. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.OriginalBridge
open Module MvPolynomial
open QuarticNet PairedFrame MixedNormalForm
open scoped BigOperators
universe u
variable {k E : Type u} [Field k] [Field E] [Algebra k E]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem paired_basis_slots_exchange
    (σ : E ≃ₐ[k] E) (hσsq : σ.trans σ = AlgEquiv.refl)
    (C : Basis (Fin 4) E (Fin 4 → E))
    (hPair : ∀ i : Fin 2, ∀ j : Fin 4,
      C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j)) :
    ∀ i j, σ (C i j) = C (pairSwap i) j := by
  have hsq (a : E) : σ (σ a) = a := by
    have h := DFunLike.congr_fun hσsq a
    change σ (σ a) = a at h
    exact h
  intro i j
  have h₀ : C 2 j = σ (C 0 j) := hPair 0 j
  have h₁ : C 3 j = σ (C 1 j) := hPair 1 j
  have h0 : pairSwap (0 : Fin 4) = 2 := by decide
  have h1 : pairSwap (1 : Fin 4) = 3 := by decide
  have h2 : pairSwap (2 : Fin 4) = 0 := by decide
  have h3 : pairSwap (3 : Fin 4) = 1 := by decide
  fin_cases i
  · change σ (C 0 j) = C (pairSwap 0) j
    rw [h0]
    exact h₀.symm
  · change σ (C 1 j) = C (pairSwap 1) j
    rw [h1]
    exact h₁.symm
  · change σ (C 2 j) = C (pairSwap 2) j
    rw [h2, h₀, hsq]
  · change σ (C 3 j) = C (pairSwap 3) j
    rw [h3, h₁, hsq]

/-- Semilinear coefficient change is the block swap in a paired frame.
This identity holds for every polynomial, not only field-valued points. -/
theorem linearSubstitution_semilinear_pairSwap
    (σ : E ≃ₐ[k] E) (M : Matrix (Fin 4) (Fin 4) E)
    (hSlots : ∀ r i, σ.toRingHom (M r i) = M r (pairSwap i))
    (G : MvPolynomial (Fin 4) E) :
    MvPolynomial.map σ.toRingHom (linearSubstitution M G) =
      MvPolynomial.rename pairSwap (linearSubstitution M (MvPolynomial.map σ.toRingHom G)) := by
  have hSub : linearSubstitution (M.map σ.toRingHom) =
      (MvPolynomial.rename pairSwap).comp (linearSubstitution M) := by
    apply MvPolynomial.algHom_ext
    intro r
    rw [AlgHom.comp_apply, linearSubstitution_X, linearSubstitution_X]
    simp only [linearCoordinate, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.map_apply, map_add, map_mul, MvPolynomial.rename_C,
      MvPolynomial.rename_X, hSlots]
    have h0 : pairSwap (0 : Fin 4) = 2 := by decide
    have h1 : pairSwap (1 : Fin 4) = 3 := by decide
    have h2 : pairSwap (2 : Fin 4) = 0 := by decide
    have h3 : pairSwap (3 : Fin 4) = 1 := by decide
    simp only [h0, h1, h2, h3]
    ring
  rw [linearSubstitution_map, hSub, AlgHom.comp_apply]

theorem original_cubic_paired_equation_exchange
    (σ : E ≃ₐ[k] E) (hσsq : σ.trans σ = AlgEquiv.refl)
    (C : Basis (Fin 4) E (Fin 4 → E))
    (hPair : ∀ i : Fin 2, ∀ j : Fin 4,
      C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j))
    (F : MvPolynomial (Fin 4) k) :
    let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
    MvPolynomial.map σ.toRingHom G = MvPolynomial.rename pairSwap G := by
  have hSlots : ∀ r i, σ.toRingHom (basisCoordinateMatrix C r i) =
      basisCoordinateMatrix C r (pairSwap i) := by
    intro r i
    exact paired_basis_slots_exchange σ hσsq C hPair i r
  have hcoeff : σ.toRingHom.comp (algebraMap k E) = algebraMap k E := by
    apply RingHom.ext
    intro a
    exact σ.commutes a
  have hFixed : MvPolynomial.map σ.toRingHom (MvPolynomial.map (algebraMap k E) F) =
      MvPolynomial.map (algebraMap k E) F := by
    rw [MvPolynomial.map_map, hcoeff]
  dsimp only
  rw [linearSubstitution_semilinear_pairSwap σ _ hSlots, hFixed]

/-- These are the actual inverse-frame linear forms in the original
ambient polynomial variables. -/
def pairedInverseCoordinates (C : Basis (Fin 4) E (Fin 4 → E)) (i : Fin 4) :
    MvPolynomial (Fin 4) E :=
  (linearSubstitutionEquiv (basisCoordinateMatrix C) (basisCoordinateMatrix_isUnit C)).symm (X i)

theorem pairedInverseCoordinates_homogeneous
    (C : Basis (Fin 4) E (Fin 4 → E)) (i : Fin 4) :
    (pairedInverseCoordinates C i).IsHomogeneous 1 := by
  change (linearSubstitution (basisCoordinateMatrix C)⁻¹ (X i)).IsHomogeneous 1
  exact linearSubstitution_homogeneous _ (MvPolynomial.isHomogeneous_X E i)

theorem pairedInverseCoordinates_ne_zero
    (C : Basis (Fin 4) E (Fin 4 → E)) (i : Fin 4) :
    pairedInverseCoordinates C i ≠ 0 := by
  let e := linearSubstitutionEquiv (basisCoordinateMatrix C) (basisCoordinateMatrix_isUnit C)
  intro h
  have hi := congrArg e h
  change e (e.symm (X i)) = e 0 at hi
  rw [e.apply_symm_apply, map_zero] at hi
  exact (MvPolynomial.X_ne_zero i) hi

/-- Coefficient conjugation exchanges the two pairs of actual original
inverse linear forms. These are the identities required by packet 002. -/
theorem pairedInverseCoordinates_exchange
    (σ : E ≃ₐ[k] E) (hσsq : σ.trans σ = AlgEquiv.refl)
    (C : Basis (Fin 4) E (Fin 4 → E))
    (hPair : ∀ i : Fin 2, ∀ j : Fin 4,
      C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j)) :
    ∀ i, MvPolynomial.map σ.toRingHom (pairedInverseCoordinates C i) =
      pairedInverseCoordinates C (pairSwap i) := by
  let M := basisCoordinateMatrix C
  let e := linearSubstitutionEquiv M (basisCoordinateMatrix_isUnit C)
  have hSlots : ∀ r i, σ.toRingHom (M r i) = M r (pairSwap i) := by
    intro r i
    exact paired_basis_slots_exchange σ hσsq C hPair i r
  intro i
  have h := linearSubstitution_semilinear_pairSwap σ M hSlots (e.symm (X i))
  change MvPolynomial.map σ.toRingHom (e (e.symm (X i))) =
    MvPolynomial.rename pairSwap (e (MvPolynomial.map σ.toRingHom (e.symm (X i)))) at h
  rw [e.apply_symm_apply, MvPolynomial.map_X] at h
  have hi : e (MvPolynomial.map σ.toRingHom (e.symm (X i))) = X (pairSwap i) := by
    apply (MvPolynomial.renameEquiv E pairSwap).injective
    change MvPolynomial.rename pairSwap (e (MvPolynomial.map σ.toRingHom (e.symm (X i)))) =
      MvPolynomial.rename pairSwap (X (pairSwap i))
    rw [← h, MvPolynomial.rename_X, pairSwap_involutive]
  apply e.injective
  exact hi.trans (e.apply_symm_apply (X (pairSwap i))).symm

/-- Actual membership in the two original projector line ideals gives
the two coordinate-line memberships in the derived frame. -/
theorem original_cubic_paired_coordinate_line_memberships
    (C : Basis (Fin 4) E (Fin 4 → E)) (P : Matrix (Fin 4) (Fin 4) E)
    (hC : matchingEdgeProjectorMatrix C = P) (FE : MvPolynomial (Fin 4) E)
    (hLines : FE ∈ (projectorLineIdeal P).toIdeal ∧
      FE ∈ (projectorLineIdeal (1 - P)).toIdeal) :
    linearSubstitution (basisCoordinateMatrix C) FE ∈
      Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)) ∧
    linearSubstitution (basisCoordinateMatrix C) FE ∈
      Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E)) := by
  let e := linearSubstitutionEquiv (basisCoordinateMatrix C) (basisCoordinateMatrix_isUnit C)
  have hLeft := hLines.1
  have hRight := hLines.2
  rw [← hC, projectorLineIdeal_eq_originalMatchingLine C] at hLeft
  rw [← hC, projectorComplementLineIdeal_eq_originalMatchingLine C] at hRight
  have hTransport (I : Ideal (MvPolynomial (Fin 4) E))
      (hmem : FE ∈ I.map e.symm.toRingHom) : e FE ∈ I := by
    obtain ⟨q, hq, heq⟩ := (Ideal.mem_map_iff_of_surjective e.symm.toRingHom e.symm.surjective).mp hmem
    have hG : e FE = q := by
      rw [← heq]
      exact e.apply_symm_apply q
    rw [hG]
    exact hq
  constructor
  · exact hTransport (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E))) hRight
  · exact hTransport (Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))) hLeft

/-- Bounded bridge from the ACTUAL original geometric projector and the
original cubic to a paired frame, actual mixed pieces, and conjugate
mixed coefficients. All coordinate certificates are outputs. -/
theorem actual_matching_exists_paired_original_cubic_normal_form
    {K : Type u} [Field K] [Algebra k K]
    (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]
    (h₂ : finrank k E = 2)
    (P : Matrix (Fin 4) (Fin 4) E) (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B)
    (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (hExchange : P.map σ.toRingHom = 1 - P)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hLines : MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal P).toIdeal ∧
      MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal (1 - P)).toIdeal) :
    ∃ C : Basis (Fin 4) E (Fin 4 → E),
      matchingEdgeProjectorMatrix C = P ∧
      (∀ i : Fin 2, ∀ j : Fin 4,
        C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j)) ∧
      let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
      G.IsHomogeneous 3 ∧
      G ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)) ∧
      G ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E)) ∧
      MvPolynomial.map σ.toRingHom G = MvPolynomial.rename pairSwap G ∧
      G = blockPiece 2 G + blockPiece 1 G ∧
      ∀ i : Fin 3, ∀ j : Fin 2,
        σ (G.coeff (leftMixedExponent i j)) = G.coeff (rightMixedExponent i j) := by
  obtain ⟨C, hC, hPair⟩ := actual_matching_exists_paired_projector_frame E P B hP σ hExchange
  have hσsq := galois_involution_of_finrank_two σ hσ h₂
  let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
  have hG : G.IsHomogeneous 3 := linearSubstitution_homogeneous _ (hF.map _)
  obtain ⟨hLeft, hRight⟩ := original_cubic_paired_coordinate_line_memberships C P hC _ hLines
  have hGExchange := original_cubic_paired_equation_exchange σ hσsq C hPair F
  refine ⟨C, hC, hPair, hG, hLeft, hRight, hGExchange,
    cubic_eq_two_mixed_block_pieces G hG hLeft hRight, ?_⟩
  exact conjugate_mixed_coefficients_exchange σ G hGExchange

end PfaffianDescent.QuadraticSkewRationality.OriginalBridge
