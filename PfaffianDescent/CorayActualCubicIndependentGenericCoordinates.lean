import PfaffianDescent.VoisinSmoothCubicEliminatedChart
import PfaffianDescent.CorayOriginalChartGenericCompatibility
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Data.Fintype.Card

/-! Genuine principal-presentation degree argument, and TWO actual
algebraically independent original cubic chart generic coordinates.
No dimension/independence/rank-two conclusion is supplied as a hypothesis.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u v

/-- A nonzero principal relation on an actual nontrivial K-algebra must
involve a variable. Removing such a variable leaves an algebraically
independent coordinate family: no polynomial in the other variables is
nonzero and divisible by the relation. -/
theorem principalPolynomialPresentation_exists_independent_coordinateSubfamily
    {K A : Type u} {σ : Type v} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (x : σ → A) (q : MvPolynomial σ K) (hq0 : q ≠ 0)
    (hker : RingHom.ker (MvPolynomial.aeval x).toRingHom =
      Ideal.span ({q} : Set (MvPolynomial σ K))) :
    ∃ t : σ, AlgebraicIndependent K (fun i : {i : σ // i ≠ t} => x i.1) := by
  classical
  have hqeval : MvPolynomial.aeval x q = 0 := by
    apply RingHom.mem_ker.mp
    exact hker.symm ▸ Ideal.subset_span (Set.mem_singleton q)
  have hvars : q.vars.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    have hqc : q = MvPolynomial.C (q.coeff 0) :=
      MvPolynomial.vars_eq_empty_iff_eq_C.mp hempty
    have hmap : MvPolynomial.aeval x q = algebraMap K A (q.coeff 0) := by
      calc
        MvPolynomial.aeval x q = MvPolynomial.aeval x (MvPolynomial.C (q.coeff 0)) :=
          congrArg (MvPolynomial.aeval x) hqc
        _ = algebraMap K A (q.coeff 0) := MvPolynomial.aeval_C x (q.coeff 0)
    have hc : algebraMap K A (q.coeff 0) = 0 := hmap.symm.trans hqeval
    have hc0 : q.coeff 0 = 0 := (algebraMap K A).injective
      (hc.trans (map_zero (algebraMap K A)).symm)
    exact hq0 (hqc.trans (by rw [hc0, map_zero]))
  obtain ⟨t, ht⟩ := hvars
  have hdegree : q.degreeOf t ≠ 0 := MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp ht
  refine ⟨t, algebraicIndependent_iff.mpr ?_⟩
  intro f hf
  by_contra hf0
  let r : MvPolynomial σ K := MvPolynomial.rename Subtype.val f
  have hr0 : r ≠ 0 := by
    intro hzero
    apply hf0
    exact (MvPolynomial.rename_injective Subtype.val Subtype.val_injective)
      (hzero.trans (map_zero (MvPolynomial.rename Subtype.val)).symm)
  have heval : MvPolynomial.aeval x r = 0 := by
    change MvPolynomial.aeval x (MvPolynomial.rename Subtype.val f) = 0
    rw [MvPolynomial.aeval_rename]
    exact hf
  have hdvd : q ∣ r := by
    apply Ideal.mem_span_singleton.mp
    rw [← hker]
    exact RingHom.mem_ker.mpr heval
  obtain ⟨z, hz⟩ := hdvd
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hr0
    rw [hz, hz0, mul_zero]
  have hrdegree : r.degreeOf t = 0 := by
    by_contra hne
    have hmem : t ∈ (MvPolynomial.rename Subtype.val f).vars :=
      MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hne
    obtain ⟨i, hi, hit⟩ := MvPolynomial.mem_vars_rename Subtype.val f hmem
    exact i.2 hit
  have heq := congrArg (fun v : MvPolynomial σ K => v.degreeOf t) hz
  rw [hrdegree, MvPolynomial.degreeOf_mul_eq hq0 hz0] at heq
  omega

attribute [local instance] MvPolynomial.gradedAlgebra

section ActualChartCuts
variable {K : Type u} [Field K]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  [IsIntegral (hypersurface p hp)] (j : Fin 4)
  [Nonempty (chartι (equationIdeal p hp) j).opensRange]

/-- Actual principal chart kernel/nonzero relation, with the original
chart algebra explicitly bound. This is an ordinary bounded proof cut. -/
private theorem independentCubicChart_principalPresentation (hp0 : p ≠ 0) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    coordinateOneEvaluation j p ≠ 0 ∧
      RingHom.ker (MvPolynomial.aeval (fun i : {i : Fin 4 // i ≠ j} =>
        chartCoordinate (equationIdeal p hp) j i.1)).toRingHom =
        Ideal.span ({coordinateOneEvaluation j p} :
          Set (MvPolynomial {i : Fin 4 // i ≠ j} K)) := by
  letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
    (chartBaseMap (equationIdeal p hp) j).toAlgebra
  have h := @smoothCubic_eliminatedChartMap_surjective_and_kernel
    K (inferInstance : Field K) p hp hp0 j
  exact ⟨h.2.2, h.2.1⟩

/-- Nontriviality is derived from the exact ACTUAL generic ring hom. -/
private theorem independentCubicChart_nontrivial :
    Nontrivial (ChartRing (equationIdeal p hp) j) :=
  (@affineChartGenericEvaluation
    (ChartRing (equationIdeal p hp) j)
    (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j)
    (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)).domain_nontrivial

/-- Original actual generic chart map, with its proved original K
coefficient diagram packaged once as an algebra hom. -/
private def independentCubicChart_genericAlgHom :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    ChartRing (equationIdeal p hp) j →ₐ[K] (hypersurface p hp).functionField := by
  letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
    (chartBaseMap (equationIdeal p hp) j).toAlgebra
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let g := @affineChartGenericEvaluation
    (ChartRing (equationIdeal p hp) j)
    (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j)
    (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  exact
    { toRingHom := g
      commutes' := fun c => by
        change g (chartBaseMap (equationIdeal p hp) j c) =
          schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp) c
        exact RingHom.congr_fun
          (@cubicChartGenericEvaluation_coefficient_eq K (inferInstance : Field K)
            p hp (inferInstance : IsIntegral (hypersurface p hp)) j
            (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)) c }

/-- The packaged hom is identity on the actual chart generic values. -/
private theorem independentCubicChart_genericAlgHom_apply
    (r : ChartRing (equationIdeal p hp) j) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    independentCubicChart_genericAlgHom p hp j r =
      @affineChartGenericEvaluation
        (ChartRing (equationIdeal p hp) j)
        (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
        (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
        (chartι (equationIdeal p hp) j)
        (isOpenImmersion_chartι (equationIdeal p hp) j)
        (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange) r := rfl

/-- Injectivity is the SAME actual generic-germ injectivity, with every
actual chart instance passed explicitly at the use site. -/
private theorem independentCubicChart_genericAlgHom_injective :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    Function.Injective (independentCubicChart_genericAlgHom p hp j) := by
  letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
    (chartBaseMap (equationIdeal p hp) j).toAlgebra
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  intro r s hrs
  apply @affineChartGenericEvaluation_injective
    (ChartRing (equationIdeal p hp) j)
    (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j)
    (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  simpa only [independentCubicChart_genericAlgHom_apply] using hrs

/-- The genuine principal-kernel degree proof is applied in the actual
chart, separately from generic transport and coordinate cardinality. -/
private theorem independentCubicChart_exists_coordinateSubfamily (hp0 : p ≠ 0) :
    letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
      (chartBaseMap (equationIdeal p hp) j).toAlgebra
    ∃ t : {i : Fin 4 // i ≠ j},
      AlgebraicIndependent K (fun i : {i : {i : Fin 4 // i ≠ j} // i ≠ t} =>
        chartCoordinate (equationIdeal p hp) j i.1.1) := by
  letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
    (chartBaseMap (equationIdeal p hp) j).toAlgebra
  letI : Nontrivial (ChartRing (equationIdeal p hp) j) :=
    independentCubicChart_nontrivial p hp j
  have h := independentCubicChart_principalPresentation p hp j hp0
  exact @principalPolynomialPresentation_exists_independent_coordinateSubfamily
    K (ChartRing (equationIdeal p hp) j) {i : Fin 4 // i ≠ j}
    (inferInstance : Field K)
    (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (independentCubicChart_nontrivial p hp j)
    ((chartBaseMap (equationIdeal p hp) j).toAlgebra)
    (fun i => chartCoordinate (equationIdeal p hp) j i.1)
    (coordinateOneEvaluation j p) h.1 h.2

/-- Genuine coordinate independence transported by the literal actual
original-K hom, not by a desired independence certificate. -/
private theorem independentCubicChart_exists_genericSubfamily (hp0 : p ≠ 0) :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    ∃ t : {i : Fin 4 // i ≠ j},
      AlgebraicIndependent K (fun i : {i : {i : Fin 4 // i ≠ j} // i ≠ t} =>
        @affineChartGenericEvaluation
          (ChartRing (equationIdeal p hp) j)
          (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
          (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
          (chartι (equationIdeal p hp) j)
          (isOpenImmersion_chartι (equationIdeal p hp) j)
          (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
          (chartCoordinate (equationIdeal p hp) j i.1.1)) := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
    (chartBaseMap (equationIdeal p hp) j).toAlgebra
  obtain ⟨t, ht⟩ := independentCubicChart_exists_coordinateSubfamily p hp j hp0
  refine ⟨t, ?_⟩
  have hm := ht.map' (f := independentCubicChart_genericAlgHom p hp j)
    (independentCubicChart_genericAlgHom_injective p hp j)
  have hfun :
      ((independentCubicChart_genericAlgHom p hp j :
          ChartRing (equationIdeal p hp) j →ₐ[K] (hypersurface p hp).functionField) :
        ChartRing (equationIdeal p hp) j → (hypersurface p hp).functionField) ∘
        (fun i : {i : {i : Fin 4 // i ≠ j} // i ≠ t} =>
          chartCoordinate (equationIdeal p hp) j i.1.1) =
      (fun i : {i : {i : Fin 4 // i ≠ j} // i ≠ t} =>
        @affineChartGenericEvaluation
          (ChartRing (equationIdeal p hp) j)
          (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
          (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
          (chartι (equationIdeal p hp) j)
          (isOpenImmersion_chartι (equationIdeal p hp) j)
          (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
          (chartCoordinate (equationIdeal p hp) j i.1.1)) := by
    funext i
    rfl
  exact hfun ▸ hm

end ActualChartCuts

/-- Pure index-count proof isolated from native cubic chart dictionaries. -/
private theorem independentCubicChart_remainingIndex_card
    (j : Fin 4) (t : {i : Fin 4 // i ≠ j}) :
    Fintype.card {i : {i : Fin 4 // i ≠ j} // i ≠ t} = 2 := by
  classical
  have hcard : Fintype.card {i : Fin 4 // i ≠ j} = 3 := by
    simp [Fintype.card_subtype_compl]
  simpa [Fintype.card_subtype_compl, hcard]

/-- TWO literal actual normalized coordinates of any nonempty original
cubic chart are algebraically independent over ORIGINAL K. The relation,
its principal kernel, its nonzero value and the generic-germ injectivity
come from the actual chart geometry; no desired certificate is assumed. -/
theorem cubicOriginalChart_exists_two_independent_generic_coordinates
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    ∃ t : {i : Fin 4 // i ≠ j},
      Fintype.card {i : {i : Fin 4 // i ≠ j} // i ≠ t} = 2 ∧
      AlgebraicIndependent K (fun i : {i : {i : Fin 4 // i ≠ j} // i ≠ t} =>
        @affineChartGenericEvaluation
          (ChartRing (equationIdeal p hp) j)
          (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
          (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
          (chartι (equationIdeal p hp) j)
          (isOpenImmersion_chartι (equationIdeal p hp) j)
          (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
          (chartCoordinate (equationIdeal p hp) j i.1.1)) := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  obtain ⟨t, ht⟩ := independentCubicChart_exists_genericSubfamily p hp j hp0
  exact ⟨t, independentCubicChart_remainingIndex_card j t, ht⟩

end PfaffianDescent.Coray
end
