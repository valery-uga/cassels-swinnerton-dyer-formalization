import PfaffianDescent.CorayActualComponentHyperplaneCartierDegree
import PfaffianDescent.CorayHomogeneousPrimeComponentGeometry
import PfaffianDescent.CorayIntegralCurveClosedSupportFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! SOURCE ONLY / UNCHECKED. A coordinate chosen at the SAME actual P
cuts the SAME original integral component in a finite whole Cartier scheme.
No Infinite, CharZero, geometric-integrality or degree premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME P itself chooses an original coordinate with nonzero class. -/
theorem projectivePoint_exists_coordinate_notMem
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : scheme C) :
    ∃ j : Fin 4, coordinate C j ∉ P.asHomogeneousIdeal := by
  classical
  by_contra h
  push_neg at h
  apply P.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant (grading C)).toIdeal ≤
    P.asHomogeneousIdeal.toIdeal
  rw [irrelevant_eq_coordinateIdeal C]
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact h j

/-- A coordinate nonvanishing at P has nonzero actual quotient class and
does not lie in C. This retains the coordinate chosen at that same P. -/
theorem coordinate_notMem_at_point_ne_zero_and_notMem_component
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : scheme C) (j : Fin 4) (hj : coordinate C j ∉ P.asHomogeneousIdeal) :
    coordinate C j ≠ 0 ∧ MvPolynomial.X j ∉ C.toIdeal := by
  have hzero : coordinate C j ≠ 0 := fun h => hj (h ▸ P.asHomogeneousIdeal.zero_mem)
  exact ⟨hzero, fun h => hzero (Ideal.Quotient.eq_zero_iff_mem.mpr h)⟩

/-- The literal coordinate-zero quotient misses P. The proof uses the
actual ambient quotient maps and literal whole equation ideal. -/
theorem coordinateCut_point_notMem_range
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : scheme C) (j : Fin 4) (hj : coordinate C j ∉ P.asHomogeneousIdeal) :
    P ∉ Set.range (schemeQuotientMap C
      (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))
      le_sup_left) := by
  let D := C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)
  let i := schemeQuotientMap C D le_sup_left
  rintro ⟨z, hz⟩
  have hamb : quotientProjMap C P ∈ Set.range (quotientProjMap D) := by
    refine ⟨z, ?_⟩
    have hc := congrArg (fun f : scheme D ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) => f z)
      (schemeQuotientMap_comp_quotientProjMap C D le_sup_left)
    exact hc.symm.trans (congrArg (quotientProjMap C) hz)
  have hDP := (quotientProjMap_mem_range_iff D (quotientProjMap C P)).mp hamb
  have hX : MvPolynomial.X j ∈ D.toIdeal := by
    apply (show (equationIdeal (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X K j)).toIdeal ≤ D.toIdeal from le_sup_right)
    exact Ideal.subset_span (Set.mem_singleton _)
  exact hj (hDP hX)

/-- Whole scheme finiteness follows from finite closed support and actual
closed-immersion injectivity. Nilpotents in the coordinate cut are retained. -/
theorem integralProjectiveComponent_coordinateCut_isFinite
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime) (P : scheme C)
    (hdim : ∀ x : scheme C, ringKrullDim ((scheme C).presheaf.stalk x) ≤ 1)
    (j : Fin 4) (hj : coordinate C j ∉ P.asHomogeneousIdeal) :
    IsFinite (toBase
      (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))) := by
  classical
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  letI : IsLocallyNoetherian (scheme C) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase C)
  letI : CompactSpace (scheme C) :=
    QuasiCompact.compactSpace_of_compactSpace (toBase C)
  letI : IsNoetherian (scheme C) := ⟨⟩
  let D := C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)
  let i := schemeQuotientMap C D le_sup_left
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion C D le_sup_left
  let S : Set (scheme C) := Set.range i
  have hclosed : IsClosed S := i.isClosedEmbedding.isClosed_range
  have hP : P ∉ S := coordinateCut_point_notMem_range C P j hj
  have hg : genericPoint (scheme C) ∉ S := by
    intro h
    have hc := closure_minimal (Set.singleton_subset_iff.mpr h) hclosed
    rw [genericPoint_closure] at hc
    exact hP (hc (Set.mem_univ P))
  have hdimNative (x : scheme C) : Ring.DimensionLEOne ((scheme C).presheaf.stalk x) := by
    letI : Ring.KrullDimLE 1 ((scheme C).presheaf.stalk x) :=
      Ring.krullDimLE_iff.mpr (hdim x)
    exact ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  have hsfinite : S.Finite :=
    (integralCurve_closed_avoiding_generic_finite_and_closedPoints
      (scheme C) hdimNative S hclosed hg).1
  have hpoints : (Set.univ : Set (scheme D)).Finite :=
    (hsfinite.preimage i.isClosedEmbedding.injective.injOn).subset
      (fun z _ => ⟨z, rfl⟩)
  letI : LocallyQuasiFinite (toBase D) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (toBase D)
      (fun _ => hpoints.subset (Set.subset_univ _))
  exact IsFinite.of_locallyQuasiFinite (toBase D)

/-- Original selected p/q geometry derives the dimension bound and hence
constructs a SAME-P coordinate, whole finite cut, and genuine Cartier charts. -/
theorem selectedProjectivePrimeComponent_exists_coordinate_finiteCartierCut
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    ∃ j : Fin 4, coordinate C j ∉ P.asHomogeneousIdeal ∧
      MvPolynomial.X j ∉ C.toIdeal ∧
      IsFinite (toBase
        (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))) ∧
      Nonempty (RegularPrincipalImmersion (schemeQuotientMap C
        (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))
        le_sup_left)) := by
  obtain ⟨j, hj⟩ := projectivePoint_exists_coordinate_notMem C P
  have hnotC := (coordinate_notMem_at_point_ne_zero_and_notMem_component C P j hj).2
  letI : C.toIdeal.IsPrime := hprime
  exact ⟨j, hj, hnotC,
    integralProjectiveComponent_coordinateCut_isFinite C hprime P
      (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
        p q hp hp0 n hq hnot C hIC) j hj,
    ⟨primeComponent_linearSection_regularPrincipalImmersion C (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X K j) hnotC⟩⟩

end PfaffianDescent.Coray
