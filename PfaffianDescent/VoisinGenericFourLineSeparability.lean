import PfaffianDescent.VoisinExplicitSeparableFourLineExample
import PfaffianDescent.VoisinCubicDiscriminantSpecialization
import AllCharacteristics.CubicLineAlgebra
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Generic separability of four cubic line restrictions

The coefficients of a universal cubic tensor are independent polynomial
variables. The four standard line restrictions have nonzero discriminant
because the explicit diagonal cubic specializes each discriminant to a
nonzero value. This file provides the coefficient-ring part of that
argument; passage to the generic coefficient field follows separately.
-/

namespace PfaffianDescent

open MvPolynomial Polynomial
open VoisinExplicitSeparableFourLineExample
open AlgebraicGeometry CategoryTheory AllCharacteristics.HomogeneousProjective

universe u

abbrev CubicTensorCoefficients (K : Type u) [CommRing K] :=
  MvPolynomial (Fin 4 × Fin 4 × Fin 4) K

noncomputable def universalCubicTensor (K : Type u) [CommRing K] :
    Cubic (CubicTensorCoefficients K) 4 := fun i => X i

theorem cubicLinePolynomial_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c : Cubic R 4) (a b : Fin 4 → R) :
    (AllCharacteristics.cubicLinePolynomial c a b).map φ =
      AllCharacteristics.cubicLinePolynomial (c.map φ)
        (fun i => φ (a i)) (fun i => φ (b i)) := by
  simp [AllCharacteristics.cubicLinePolynomial, Cubic.eval_map,
    Cubic.mixed_map]

noncomputable def diagonalCubicTensorSpecialization
    (K : Type u) [Field K] : CubicTensorCoefficients K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (c₀ (K := K))

theorem universalCubicTensor_map_diagonal
    (K : Type u) [Field K] :
    (universalCubicTensor K).map (diagonalCubicTensorSpecialization K) =
      c₀ (K := K) := by
  funext i
  simp [universalCubicTensor, diagonalCubicTensorSpecialization, Cubic.map]

noncomputable def universalFourLineBase
    (K : Type u) [Field K] : Fin 4 → CubicTensorCoefficients K :=
  fun i => C (((Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K)) i)

noncomputable def universalFourLineDirection
    (K : Type u) [Field K] (i j : Fin 2) :
    Fin 4 → CubicTensorCoefficients K :=
  fun k => C ((lineDirection (L := K) i j) k)

noncomputable def universalFourLinePolynomial
    (K : Type u) [Field K] (i j : Fin 2) :
    (CubicTensorCoefficients K)[X] :=
  AllCharacteristics.cubicLinePolynomial (universalCubicTensor K)
    (universalFourLineBase K) (universalFourLineDirection K i j)

theorem universalFourLinePolynomial_map_diagonal
    (K : Type u) [Field K] (i j : Fin 2) :
    (universalFourLinePolynomial K i j).map
      (diagonalCubicTensorSpecialization K) =
      AllCharacteristics.cubicLinePolynomial (c₀ (K := K))
        (Pi.single 0 1) (lineDirection i j) := by
  rw [universalFourLinePolynomial, cubicLinePolynomial_map,
    universalCubicTensor_map_diagonal]
  congr 1 <;> funext k <;>
    simp [universalFourLineBase, universalFourLineDirection,
      diagonalCubicTensorSpecialization]

theorem universalCubicTensor_base_eval_ne_zero
    (K : Type u) [Field K] :
    (universalCubicTensor K).eval (universalFourLineBase K) ≠ 0 := by
  let φ := diagonalCubicTensorSpecialization K
  have h := Cubic.eval_map φ (universalCubicTensor K) (universalFourLineBase K)
  rw [universalCubicTensor_map_diagonal] at h
  have ha : (fun i => φ (universalFourLineBase K i)) =
      (Pi.single 0 1 : Fin 4 → K) := by
    funext i
    simp [φ, universalFourLineBase, diagonalCubicTensorSpecialization]
  rw [ha] at h
  intro hzero
  rw [hzero, map_zero] at h
  exact c₀_base_ne_zero h

theorem universalFourLinePolynomial_degree_three
    (K : Type u) [Field K] (i j : Fin 2) :
    (universalFourLinePolynomial K i j).degree = 3 := by
  apply (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 3)).mpr
  exact AllCharacteristics.cubicLinePolynomial_natDegree
    (universalCubicTensor K) (universalFourLineBase K)
    (universalFourLineDirection K i j)
    (universalCubicTensor_base_eval_ne_zero K)

/-- The four discriminants of the universal cubic tensor's standard line
restrictions are nonzero elements of its polynomial coefficient ring. -/
theorem universalFourLinePolynomial_discr_ne_zero
    (K : Type u) [Field K] [CharZero K] (i j : Fin 2) :
    (universalFourLinePolynomial K i j).discr ≠ 0 := by
  let φ := diagonalCubicTensorSpecialization K
  have hmap : ((universalFourLinePolynomial K i j).map φ).degree = 3 := by
    rw [universalFourLinePolynomial_map_diagonal,
      c₀_linePolynomial_eq]
    exact degree_X_pow_add_C (by decide : 0 < 3) _
  apply cubic_discr_ne_zero_of_specialization φ
    (universalFourLinePolynomial K i j)
    (universalFourLinePolynomial_degree_three K i j) hmap
  rw [universalFourLinePolynomial_map_diagonal]
  exact c₀_four_line_discr_ne_zero i j

/-- Over the fraction field of the independent cubic-tensor coefficients,
all four standard line restrictions are separable. -/
theorem universalFourLinePolynomial_generic_separable
    (K : Type u) [Field K] [CharZero K] (i j : Fin 2) :
    ((universalFourLinePolynomial K i j).map
      (algebraMap (CubicTensorCoefficients K)
        (FractionRing (CubicTensorCoefficients K)))).Separable := by
  let T := CubicTensorCoefficients K
  let L := FractionRing T
  let φ : T →+* L := algebraMap T L
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective T L
  let f := universalFourLinePolynomial K i j
  have hf : f.degree = 3 := universalFourLinePolynomial_degree_three K i j
  have hmap : (f.map φ).degree = 3 := by
    rw [degree_map_eq_of_injective hφ]
    exact hf
  have hdisc : (f.map φ).discr ≠ 0 := by
    rw [cubic_discr_map_of_degree_three φ f hf hmap]
    intro hzero
    exact universalFourLinePolynomial_discr_ne_zero K i j
      (hφ (by simpa using hzero))
  exact polynomial_separable_of_discr_ne_zero (f.map φ)
    (by rw [hmap]; decide) hdisc

noncomputable def genericCubicTensor
    (K : Type u) [Field K] :
    Cubic (FractionRing (CubicTensorCoefficients K)) 4 :=
  (universalCubicTensor K).map
    (algebraMap (CubicTensorCoefficients K)
      (FractionRing (CubicTensorCoefficients K)))

noncomputable def genericFourLineBase
    (K : Type u) [Field K] :
    Fin 4 → FractionRing (CubicTensorCoefficients K) :=
  fun i => algebraMap (CubicTensorCoefficients K)
    (FractionRing (CubicTensorCoefficients K)) (universalFourLineBase K i)

noncomputable def genericFourLineDirection
    (K : Type u) [Field K] (i j : Fin 2) :
    Fin 4 → FractionRing (CubicTensorCoefficients K) :=
  fun k => algebraMap (CubicTensorCoefficients K)
    (FractionRing (CubicTensorCoefficients K))
      (universalFourLineDirection K i j k)

theorem genericCubicTensor_base_eval_ne_zero
    (K : Type u) [Field K] :
    (genericCubicTensor K).eval (genericFourLineBase K) ≠ 0 := by
  let T := CubicTensorCoefficients K
  let L := FractionRing T
  let φ : T →+* L := algebraMap T L
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective T L
  have h := Cubic.eval_map φ (universalCubicTensor K) (universalFourLineBase K)
  change (genericCubicTensor K).eval (genericFourLineBase K) =
    φ ((universalCubicTensor K).eval (universalFourLineBase K)) at h
  rw [h]
  simpa using hφ.ne (universalCubicTensor_base_eval_ne_zero K)

theorem genericCubicTensor_fourLine_separable
    (K : Type u) [Field K] [CharZero K] (i j : Fin 2) :
    (AllCharacteristics.cubicLinePolynomial (genericCubicTensor K)
      (genericFourLineBase K) (genericFourLineDirection K i j)).Separable := by
  unfold genericCubicTensor genericFourLineBase genericFourLineDirection
  rw [← cubicLinePolynomial_map]
  exact universalFourLinePolynomial_generic_separable K i j

/-- Separable four-line restrictions remain separable over any extension of
the generic coefficient field, in particular over its algebraic closure. -/
theorem genericCubicTensor_fourLine_separable_baseChange
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L)
    (i j : Fin 2) :
    (AllCharacteristics.cubicLinePolynomial
      ((genericCubicTensor K).map φ)
      (fun k => φ (genericFourLineBase K k))
      (fun k => φ (genericFourLineDirection K i j k))).Separable := by
  rw [← cubicLinePolynomial_map]
  exact (genericCubicTensor_fourLine_separable K i j).map

theorem genericCubicTensor_base_eval_ne_zero_baseChange
    (K : Type u) [Field K]
    {L : Type u} [Field L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ((genericCubicTensor K).map φ).eval
      (fun k => φ (genericFourLineBase K k)) ≠ 0 := by
  rw [Cubic.eval_map]
  simpa using φ.injective.ne (genericCubicTensor_base_eval_ne_zero K)

/-- Over an algebraic closure of the generic coefficient field, the four
standard line sections each have three distinct affine roots of the cubic,
with their line-parameter representations retained. -/
theorem exists_generic_four_line_root_triples
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ∃ x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L,
      (∀ i j, Function.Injective (x i j)) ∧
      (∀ i j k, ((genericCubicTensor K).map φ).eval (x i j k) = 0) ∧
      (∀ i j k, ∃ t : L,
        x i j k = t • (fun m => φ (genericFourLineBase K m)) +
          (fun m => φ (genericFourLineDirection K i j m))) ∧
      (∀ i j (s t : L),
        ((genericCubicTensor K).map φ).eval
          (s • (fun m => φ (genericFourLineBase K m)) +
            t • (fun m => φ (genericFourLineDirection K i j m))) = 0 →
        s • (fun m => φ (genericFourLineBase K m)) +
          t • (fun m => φ (genericFourLineDirection K i j m)) = 0 ∨
          ∃ (k : Fin 3) (u : L),
            s • (fun m => φ (genericFourLineBase K m)) +
              t • (fun m => φ (genericFourLineDirection K i j m)) = u • x i j k) := by
  classical
  have hlocal : ∀ i j : Fin 2,
      ∃ y : Fin 3 → Fin 4 → L,
        (∀ k, ((genericCubicTensor K).map φ).eval (y k) = 0) ∧
        Function.Injective y ∧
        (∀ k, ∃ t : L,
          y k = t • (fun m => φ (genericFourLineBase K m)) +
            (fun m => φ (genericFourLineDirection K i j m))) ∧
        ∀ s t : L,
          ((genericCubicTensor K).map φ).eval
            (s • (fun m => φ (genericFourLineBase K m)) +
              t • (fun m => φ (genericFourLineDirection K i j m))) = 0 →
          s • (fun m => φ (genericFourLineBase K m)) +
            t • (fun m => φ (genericFourLineDirection K i j m)) = 0 ∨
            ∃ (k : Fin 3) (u : L), s • (fun m => φ (genericFourLineBase K m)) +
              t • (fun m => φ (genericFourLineDirection K i j m)) = u • y k := by
    intro i j
    exact AllCharacteristics.exists_three_cubic_line_points_cover_of_separable
      ((genericCubicTensor K).map φ)
      (fun m => φ (genericFourLineBase K m))
      (fun m => φ (genericFourLineDirection K i j m))
      (genericCubicTensor_base_eval_ne_zero_baseChange K φ)
      (genericCubicTensor_fourLine_separable_baseChange K φ i j)
  choose x hzero hinj hform hcover using hlocal
  exact ⟨x, hinj, hzero, hform, hcover⟩

theorem genericFourLineBase_baseChange_eq
    (K : Type u) [Field K]
    {L : Type u} [Field L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    (fun m => φ (genericFourLineBase K m)) =
      (Pi.single 0 1 : Fin 4 → L) := by
  funext m
  fin_cases m <;>
    simp [genericFourLineBase, universalFourLineBase, Pi.single]

theorem genericFourLineDirection_baseChange_eq
    (K : Type u) [Field K]
    {L : Type u} [Field L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L)
    (i j : Fin 2) :
    (fun m => φ (genericFourLineDirection K i j m)) =
      lineDirection i j := by
  funext m
  fin_cases i <;> fin_cases j <;> fin_cases m <;>
    simp [genericFourLineDirection, universalFourLineDirection,
      lineDirection, Pi.single]

/-- The twelve roots of the universal generic cubic on the four standard
lines are distinct as projective points over an algebraic closure. -/
theorem exists_generic_twelve_projectively_distinct_roots
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ∃ x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L,
      (∀ i j k, ((genericCubicTensor K).map φ).eval (x i j k) = 0) ∧
      (∀ i j k, ∃ t : L, x i j k =
        t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) ∧
      (∀ {i j i' j' : Fin 2} {k k' : Fin 3},
        (i, j, k) ≠ (i', j', k') → ∀ c : L,
          c • x i j k ≠ x i' j' k') := by
  obtain ⟨x, hinj, hzero, hform, -⟩ :=
    exists_generic_four_line_root_triples K φ
  rw [genericFourLineBase_baseChange_eq K φ] at hform
  have hform' : ∀ i j k, ∃ t : L,
      x i j k = t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j := by
    intro i j k
    obtain ⟨t, ht⟩ := hform i j k
    refine ⟨t, ?_⟩
    rwa [genericFourLineDirection_baseChange_eq K φ i j] at ht
  refine ⟨x, hzero, hform', ?_⟩
  intro i j i' j' k k' hindex c
  exact shearedFourLines_twelve_roots_projectively_distinct
    (Pi.single 0 1 : Fin 4 → L) (by simp) x hinj hform' hindex c

theorem standard_split_quadrics_zero_on_line
    {L : Type u} [Field L] (i j : Fin 2) (t : L) :
    ((X 1 * X 2 : MvPolynomial (Fin 4) L).eval
      (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) = 0) ∧
    ((X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval
      (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) = 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [lineDirection, Pi.single, MvPolynomial.eval_mul,
      MvPolynomial.eval_add]

/-- The twelve generic roots also satisfy the two standard split quadrics. -/
theorem exists_generic_twelve_split_intersection_roots
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ∃ x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L,
      (∀ i j k,
        ((genericCubicTensor K).map φ).toMvPolynomial.eval (x i j k) = 0 ∧
        (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (x i j k) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval
          (x i j k) = 0) ∧
      (∀ {i j i' j' : Fin 2} {k k' : Fin 3},
        (i, j, k) ≠ (i', j', k') → ∀ c : L,
          c • x i j k ≠ x i' j' k') := by
  obtain ⟨x, hzero, hform, hdistinct⟩ :=
    exists_generic_twelve_projectively_distinct_roots K φ
  refine ⟨x, ?_, hdistinct⟩
  intro i j k
  obtain ⟨t, ht⟩ := hform i j k
  rw [ht]
  have hsplit := standard_split_quadrics_zero_on_line i j t
  have hp := hzero i j k
  rw [ht] at hp
  have hev := Cubic.eval_toMvPolynomial (RingHom.id L)
    ((genericCubicTensor K).map φ)
    (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j)
  change ((genericCubicTensor K).map φ).toMvPolynomial.eval
    (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) =
      ((genericCubicTensor K).map φ).eval
        (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) at hev
  exact ⟨hev.trans hp,
    hsplit.1, hsplit.2⟩

theorem cubic_toMvPolynomial_isHomogeneous_three
    {L : Type u} [CommRing L] (c : Cubic L 4) :
    c.toMvPolynomial.IsHomogeneous 3 := by
  classical
  unfold Cubic.toMvPolynomial
  apply IsHomogeneous.sum
  intro i hi
  convert (((isHomogeneous_C (Fin 4) (c i)).mul
    (isHomogeneous_X L i.1)).mul
      (isHomogeneous_X L i.2.1)).mul
      (isHomogeneous_X L i.2.2) using 1

theorem cubic_toMvPolynomial_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c : Cubic R 4) :
    c.toMvPolynomial.map φ = (c.map φ).toMvPolynomial := by
  simp [Cubic.toMvPolynomial, Cubic.map]

theorem genericCubicTensor_baseChange_standard_point_ne_zero
    (K : Type u) [Field K]
    {L : Type u} [Field L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ((genericCubicTensor K).map φ).toMvPolynomial.eval
      (Pi.single 0 1 : Fin 4 → L) ≠ 0 := by
  have h := genericCubicTensor_base_eval_ne_zero_baseChange K φ
  rw [genericFourLineBase_baseChange_eq K φ] at h
  have hev := Cubic.eval_toMvPolynomial (RingHom.id L)
    ((genericCubicTensor K).map φ) (Pi.single 0 1 : Fin 4 → L)
  change ((genericCubicTensor K).map φ).toMvPolynomial.eval
    (Pi.single 0 1 : Fin 4 → L) =
      ((genericCubicTensor K).map φ).eval
        (Pi.single 0 1 : Fin 4 → L) at hev
  exact hev.symm ▸ h

/-- The same split quadrics cut a finite scheme on the generic cubic after
base change to an algebraic closure. -/
theorem generic_split_intersection_finite
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      ((genericCubicTensor K).map φ).toMvPolynomial
      (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
      (cubic_toMvPolynomial_isHomogeneous_three _)
      ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
      ((isHomogeneous_X L 3).mul
        (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
          (isHomogeneous_X L 3))))) := by
  apply standardFourLines_finite
  change ((genericCubicTensor K).map φ).toMvPolynomial.eval
    (Pi.single 0 1 : Fin 4 → L) ≠ 0
  exact genericCubicTensor_baseChange_standard_point_ne_zero K φ

end PfaffianDescent
