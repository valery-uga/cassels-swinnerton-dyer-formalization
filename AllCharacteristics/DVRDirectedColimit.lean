import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Directed colimits of discrete valuation rings

This file records the algebraic part of the limit-stage construction in a
Cohen-ring tower.  A directed colimit of discrete valuation rings is again a
discrete valuation ring when the transition maps are injective and carry a
chosen uniformizer to the chosen uniformizer at every later stage.
-/

namespace AllCharacteristics

universe u v

section

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (f : ∀ i j (_ : i ≤ j), A i →+* A j)
variable [DirectedSystem A (f · · ·)]

/-- Injective transition maps preserve the domain property in a directed ring
colimit. -/
theorem directLimit_isDomain_of_injective
    [∀ i, IsDomain (A i)]
    (hinj : ∀ i j (h : i ≤ j), Function.Injective (f i j h)) :
    IsDomain (DirectLimit A f) := by
  letI : NoZeroDivisors (DirectLimit A f) := by
    constructor
    intro x y hxy
    induction x, y using DirectLimit.induction₂ f with
    | _ i x y =>
      rw [DirectLimit.zero_def i, DirectLimit.mul_def] at hxy
      have hprod : x * y = 0 := DirectLimit.mk_injective f hinj i hxy
      rcases mul_eq_zero.mp hprod with h | h
      · subst x
        exact Or.inl (DirectLimit.zero_def i).symm
      · subst y
        exact Or.inr (DirectLimit.zero_def i).symm
  exact NoZeroDivisors.to_isDomain (DirectLimit A f)

/-- The common image of a compatible family of uniformizers. -/
noncomputable def directLimitUniformizer (i : ι) (π : ∀ i, A i) : DirectLimit A f :=
  DirectLimit.Ring.of A f i (π i)

/-- The image of a compatible uniformizer is independent of the stage. -/
theorem directLimitUniformizer_eq
    (π : ∀ i, A i)
    (hmap : ∀ i j (h : i ≤ j), f i j h (π i) = π j)
    {i j : ι} (hij : i ≤ j) :
    directLimitUniformizer A f i π = directLimitUniformizer A f j π := by
  change DirectLimit.Ring.of A f i (π i) = DirectLimit.Ring.of A f j (π j)
  rw [← hmap i j hij, DirectLimit.Ring.of_f]

/-- The image of a compatible uniformizer is a nonunit in an injective
directed colimit. -/
theorem directLimitUniformizer_not_isUnit
    [∀ i, IsDomain (A i)]
    (π : ∀ i, A i)
    (hπ : ∀ i, Irreducible (π i))
    (hmap : ∀ i j (h : i ≤ j), f i j h (π i) = π j)
    (hinj : ∀ i j (h : i ≤ j), Function.Injective (f i j h))
    (i₀ : ι) :
    ¬ IsUnit (directLimitUniformizer A f i₀ π) := by
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk f y
  rw [hx] at hy
  have hy' : DirectLimit.Ring.of A f i₀ (π i₀) *
      DirectLimit.Ring.of A f i x = 1 := by
    exact hy
  obtain ⟨j, hi₀j, hij⟩ := exists_ge_ge i₀ i
  have hprodDL : (⟦⟨j, f i₀ j hi₀j (π i₀) * f i j hij x⟩⟧ : DirectLimit A f) =
      ⟦⟨j, 1⟩⟧ := by
    calc
      (⟦⟨j, f i₀ j hi₀j (π i₀) * f i j hij x⟩⟧ : DirectLimit A f) =
          DirectLimit.Ring.of A f j (f i₀ j hi₀j (π i₀)) *
            DirectLimit.Ring.of A f j (f i j hij x) := by
              change (⟦⟨j, f i₀ j hi₀j (π i₀) * f i j hij x⟩⟧ : DirectLimit A f) =
                (⟦⟨j, f i₀ j hi₀j (π i₀)⟩⟧ : DirectLimit A f) *
                  (⟦⟨j, f i j hij x⟩⟧ : DirectLimit A f)
              rw [DirectLimit.mul_def]
      _ = DirectLimit.Ring.of A f i₀ (π i₀) * DirectLimit.Ring.of A f i x := by
            rw [DirectLimit.Ring.of_f, DirectLimit.Ring.of_f]
      _ = 1 := hy'
      _ = ⟦⟨j, 1⟩⟧ := DirectLimit.one_def j
  have hprod : f i₀ j hi₀j (π i₀) * f i j hij x = 1 :=
    DirectLimit.mk_injective f hinj j hprodDL
  rw [hmap i₀ j hi₀j] at hprod
  apply (hπ j).not_isUnit
  exact IsUnit.of_mul_eq_one _ hprod

/-- The common image of compatible uniformizers is irreducible. -/
theorem directLimitUniformizer_irreducible
    [∀ i, IsDomain (A i)]
    (π : ∀ i, A i)
    (hπ : ∀ i, Irreducible (π i))
    (hmap : ∀ i j (h : i ≤ j), f i j h (π i) = π j)
    (hinj : ∀ i j (h : i ≤ j), Function.Injective (f i j h))
    (i₀ : ι) :
    Irreducible (directLimitUniformizer A f i₀ π) := by
  refine ⟨directLimitUniformizer_not_isUnit A f π hπ hmap hinj i₀, ?_⟩
  intro a b hab
  induction a, b using DirectLimit.induction₂ f with
  | _ i a b =>
    change DirectLimit.Ring.of A f i₀ (π i₀) =
      DirectLimit.Ring.of A f i a * DirectLimit.Ring.of A f i b at hab
    change (⟦⟨i₀, π i₀⟩⟧ : DirectLimit A f) =
      (⟦⟨i, a⟩⟧ : DirectLimit A f) * (⟦⟨i, b⟩⟧ : DirectLimit A f) at hab
    rw [DirectLimit.mul_def] at hab
    rcases Quotient.exact hab with ⟨j, hi₀j, hij, heq⟩
    rw [map_mul, hmap] at heq
    rcases (hπ j).isUnit_or_isUnit heq with ha | hb
    · left
      change IsUnit (DirectLimit.Ring.of A f i a)
      rw [← DirectLimit.Ring.of_f hij a]
      exact IsUnit.map (DirectLimit.Ring.of A f j) ha
    · right
      change IsUnit (DirectLimit.Ring.of A f i b)
      rw [← DirectLimit.Ring.of_f hij b]
      exact IsUnit.map (DirectLimit.Ring.of A f j) hb

/-- The common image of compatible uniformizers does not depend on either
chosen stage. -/
theorem directLimitUniformizer_eq_any
    (π : ∀ i, A i)
    (hmap : ∀ i j (h : i ≤ j), f i j h (π i) = π j)
    (i i' : ι) :
    directLimitUniformizer A f i π = directLimitUniformizer A f i' π := by
  obtain ⟨j, hij, hi'j⟩ := exists_ge_ge i i'
  calc
    directLimitUniformizer A f i π = directLimitUniformizer A f j π :=
      directLimitUniformizer_eq A f π hmap hij
    _ = directLimitUniformizer A f i' π :=
      (directLimitUniformizer_eq A f π hmap hi'j).symm

/-- A directed colimit of DVRs is a DVR if its injective transition maps
preserve a compatible choice of uniformizer.

The conclusion binds the domain instance produced by
`directLimit_isDomain_of_injective`; callers can install that same instance
before applying the theorem. -/
theorem directLimit_isDiscreteValuationRing_of_injective_uniformizers
    [∀ i, IsDomain (A i)] [∀ i, IsDiscreteValuationRing (A i)]
    (π : ∀ i, A i)
    (hπ : ∀ i, Irreducible (π i))
    (hmap : ∀ i j (h : i ≤ j), f i j h (π i) = π j)
    (hinj : ∀ i j (h : i ≤ j), Function.Injective (f i j h))
    (i₀ : ι) :
    let _ : IsDomain (DirectLimit A f) := directLimit_isDomain_of_injective A f hinj
    IsDiscreteValuationRing (DirectLimit A f) := by
  letI : IsDomain (DirectLimit A f) := directLimit_isDomain_of_injective A f hinj
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨directLimitUniformizer A f i₀ π,
    directLimitUniformizer_irreducible A f π hπ hmap hinj i₀, ?_⟩
  intro y hy
  induction y using DirectLimit.induction f with
  | _ i y =>
    have hy' : y ≠ 0 := by
      intro hy'
      apply hy
      subst y
      exact (DirectLimit.zero_def i).symm
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy' (hπ i)
    refine ⟨n, ?_⟩
    change Associated (directLimitUniformizer A f i₀ π ^ n)
      (DirectLimit.Ring.of A f i y)
    rw [directLimitUniformizer_eq_any A f π hmap i₀ i, hu, map_mul, map_pow]
    change Associated ((DirectLimit.Ring.of A f i (π i)) ^ n)
      (↑(Units.map (DirectLimit.Ring.of A f i).toMonoidHom u) *
        (DirectLimit.Ring.of A f i (π i)) ^ n)
    exact (associated_unit_mul_left _ _
      (Units.map (DirectLimit.Ring.of A f i).toMonoidHom u).isUnit).symm

end

end AllCharacteristics
