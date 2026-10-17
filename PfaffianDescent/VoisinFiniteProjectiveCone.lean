import PfaffianDescent.VoisinProperQuasiFiniteFibreOpen
import AllCharacteristics.ProjectivePointCoordinates
import AllCharacteristics.NormalizedChartGeneration
import Mathlib.RingTheory.Nullstellensatz

/-!
# Finiteness from finitely many projective zero directions

The goal is to turn a finite list of homogeneous zero directions over an
algebraically closed field into finiteness of the actual projective scheme.
This file first records the needed uniqueness of normalized chart points.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_field_point_eq_of_chart_coordinates
    {K : Type u} [Field K] {σ : Type}
    (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    (j : σ) (g₁ g₂ : ChartRing I j →+* K)
    (hbase₁ : g₁.comp (chartBaseMap I j) = RingHom.id K)
    (hbase₂ : g₂.comp (chartBaseMap I j) = RingHom.id K)
    (hcoord : ∀ i, g₁ (chartCoordinate I j i) =
      g₂ (chartCoordinate I j i)) :
    Spec.map (CommRingCat.ofHom g₁) ≫ chartι I j =
      Spec.map (CommRingCat.ofHom g₂) ≫ chartι I j := by
  have hg : g₁ = g₂ := by
    apply RingHom.ext
    intro a
    obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j a
    change g₁ (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      g₂ (p.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂,
      hbase₁, hbase₂]
    congr 1
    funext i
    exact hcoord i
  rw [hg]

/-- If every nonzero homogeneous zero of a projective ideal lies on one of
finitely many lines through the origin, the actual projective scheme is finite
over the algebraically closed field. No radicality is required. -/
theorem isFinite_projective_of_finite_cone_coverage
    {K : Type u} [Field K] [IsAlgClosed K]
    {ι : Type*} [Finite ι]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : ι → Fin 4 → K)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I.toIdeal,
      y = 0 ∨ ∃ (i : ι) (c : K), y = c • x i) :
    IsFinite (toBase I) := by
  classical
  let P := {q : Spec (.of K) ⟶ scheme I // q ≫ toBase I = 𝟙 _}
  have hwitness : ∀ q : P,
      ∃ (j : Fin 4) (i : ι) (g : ChartRing I j →+* K) (c : K),
        g.comp (chartBaseMap I j) = RingHom.id K ∧
        Spec.map (CommRingCat.ofHom g) ≫ chartι I j = q.1 ∧
        ∀ k, g (chartCoordinate I j k) = c * x i k := by
    intro q
    obtain ⟨j, g, hbase, hq⟩ :=
      exists_chart_hom_eq_of_point I (RingHom.id K) q.1 (by
        have hid : Spec.map (CommRingCat.ofHom (RingHom.id K)) =
            𝟙 (Spec (.of K)) := by simpa using (Spec.map_id (.of K))
        rw [hid]
        exact q.2)
    let y : Fin 4 → K := fun k ↦ g (chartCoordinate I j k)
    have hyj : y j = 1 := by simp [y, chartCoordinate_self]
    have hyI : y ∈ MvPolynomial.zeroLocus K I.toIdeal := by
      intro p hp
      have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hp)
      rw [MvPolynomial.hom_eval₂, hbase, map_zero] at h
      simpa [y] using h
    rcases hcover y hyI with hy0 | ⟨i, c, hy⟩
    · have : (1 : K) = 0 := by rw [← hyj, hy0]; rfl
      exact False.elim (one_ne_zero this)
    · refine ⟨j, i, g, c, hbase, hq, ?_⟩
      intro k
      have hk := congrFun hy k
      simpa [y] using hk
  let w : P → Fin 4 × ι := fun q ↦
    let z := Classical.choose (hwitness q)
    (z, Classical.choose (Classical.choose_spec (hwitness q)))
  have hw : ∀ q : P, ∃ (g : ChartRing I (w q).1 →+* K) (c : K),
      g.comp (chartBaseMap I (w q).1) = RingHom.id K ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I (w q).1 = q.1 ∧
      ∀ k, g (chartCoordinate I (w q).1 k) = c * x (w q).2 k := by
    intro q
    exact Classical.choose_spec (Classical.choose_spec (hwitness q))
  have hwinj : Function.Injective w := by
    intro q₁ q₂ heq
    obtain ⟨g₁, c₁, hb₁, hq₁, hc₁⟩ := hw q₁
    have hw₂ : ∃ (g : ChartRing I (w q₁).1 →+* K) (c : K),
        g.comp (chartBaseMap I (w q₁).1) = RingHom.id K ∧
        Spec.map (CommRingCat.ofHom g) ≫ chartι I (w q₁).1 = q₂.1 ∧
        ∀ k, g (chartCoordinate I (w q₁).1 k) = c * x (w q₁).2 k := by
      have h := hw q₂
      rw [← heq] at h
      exact h
    obtain ⟨g₂, c₂, hb₂, hq₂, hc₂⟩ := hw₂
    have hone₁ : c₁ * x (w q₁).2 (w q₁).1 = 1 := by
      rw [← hc₁]
      simp [chartCoordinate_self]
    have hone₂ : c₂ * x (w q₁).2 (w q₁).1 = 1 := by
      rw [← hc₂]
      simp [chartCoordinate_self]
    have hcx : x (w q₁).2 (w q₁).1 ≠ 0 := by
      intro hz
      simp [hz] at hone₁
    have hcc : c₁ = c₂ :=
      mul_right_cancel₀ hcx (hone₁.trans hone₂.symm)
    have hcoords : ∀ k, g₁ (chartCoordinate I (w q₁).1 k) =
        g₂ (chartCoordinate I (w q₁).1 k) := by
      intro k
      rw [hc₁, hc₂, hcc]
    apply Subtype.ext
    rw [← hq₁, ← hq₂]
    exact projective_field_point_eq_of_chart_coordinates
      I (w q₁).1 g₁ g₂ hb₁ hb₂ hcoords
  haveI : Finite P := Finite.of_injective w hwinj
  exact isFinite_of_proper_over_algClosed_of_finite_fieldPoints
    (toBase I) (show Finite P from inferInstance)

end PfaffianDescent
