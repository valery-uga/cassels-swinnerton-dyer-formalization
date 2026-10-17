import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.PolynomialCoordinateOne
import AllCharacteristics.ClosedHypersurfaceDimension
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Dimension at closed points of projective hypersurfaces in three-space

Coordinate normalization preserves nonzero homogeneous equations. Each actual
projective chart is therefore a nonzero affine hypersurface in three variables,
and its closed-point local rings have dimension two.
-/

noncomputable section
set_option linter.style.haveILetI false
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
namespace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
/-- Normalization at a coordinate cannot annihilate a nonzero homogeneous form. -/
theorem coordinateOneEvaluation_ne_zero_of_homogeneous
    {σ : Type} (j : σ) (p : MvPolynomial σ K) {d : ℕ}
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) : coordinateOneEvaluation j p ≠ 0 := by
  intro hzero
  let I : HomogeneousIdeal (homogeneousSubmodule σ K) := ⊥
  have hmem : p ∈ coordinateOneIdeal j := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (coordinateOneQuotientEquiv j).injective
    simpa only [coordinateOneQuotientEquiv_mk, map_zero] using hzero
  have hchart : eval₂Hom (chartBaseMap I j) (chartCoordinate I j) p = 0 := by
    change p ∈ RingHom.ker (eval₂Hom (chartBaseMap I j) (chartCoordinate I j))
    rw [chartEvaluation_ker]
    exact (le_sup_right : coordinateOneIdeal j ≤ chartPresentationIdeal I j) hmem
  rw [show eval₂Hom (chartBaseMap I j) (chartCoordinate I j) p =
    p.eval₂ (chartBaseMap I j) (chartCoordinate I j) from rfl,
    eval₂_chartCoordinate_eq_fraction I j p hp] at hchart
  have hloc := congrArg HomogeneousLocalization.val hchart
  rw [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk'] at hloc
  obtain ⟨s, hs⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hloc
  haveI : IsDomain (CoordinateRing I) := by
    change IsDomain (MvPolynomial σ K ⧸ (⊥ : Ideal _))
    infer_instance
  have hz : coordinate I j ≠ 0 := by
    intro hz
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
    change (X j : MvPolynomial σ K) ∈ (⊥ : Ideal _) at hm
    exact X_ne_zero j hm
  obtain ⟨n, hn⟩ := s.2
  have hs0 : (s : CoordinateRing I) ≠ 0 := by
    rw [← hn]
    exact pow_ne_zero n hz
  have hpq : Ideal.Quotient.mk I.toIdeal p = 0 := (mul_eq_zero.mp hs).resolve_left hs0
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hpq
  change p ∈ (⊥ : Ideal _) at hm
  exact hp0 hm

set_option backward.isDefEq.respectTransparency false in
/-- Eliminating the coordinate set to one commutes with imposing an equation. -/
noncomputable def coordinateOneHypersurfaceQuotientEquiv
    {σ : Type} (j : σ) (p : MvPolynomial σ K) :
    (MvPolynomial σ K ⧸ (Ideal.span {p} ⊔ coordinateOneIdeal j)) ≃ₐ[K]
      (MvPolynomial {i : σ // i ≠ j} K ⧸ Ideal.span {coordinateOneEvaluation j p}) := by
  let I : Ideal (MvPolynomial σ K) := coordinateOneIdeal j
  let J : Ideal (MvPolynomial σ K) := Ideal.span {p}
  let E := coordinateOneQuotientEquiv (R := K) j
  have hJ : Ideal.span {coordinateOneEvaluation j p} =
      (J.map (Ideal.Quotient.mkₐ K I)).map E.toRingHom := by
    simp [J, I, Ideal.map_span, E, coordinateOneQuotientEquiv_mk]
  exact (Ideal.quotientEquivAlgOfEq K (sup_comm J I)).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ K I J).symm.trans
      (Ideal.quotientEquivAlg (J.map (Ideal.Quotient.mkₐ K I))
        (Ideal.span {coordinateOneEvaluation j p}) E hJ))

set_option backward.isDefEq.respectTransparency false in
/-- An actual projective hypersurface chart is a nonzero three-variable hypersurface. -/
theorem exists_hypersurfaceChart_three_variable_presentation
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0) (j : Fin 4) :
    ∃ f : MvPolynomial (Fin 3) K, f ≠ 0 ∧
      Nonempty (ChartRing (equationIdeal p hp) j ≃+*
        (MvPolynomial (Fin 3) K ⧸ Ideal.span {f})) := by
  classical
  have hcard : Fintype.card {i : Fin 4 // i ≠ j} = 3 := by
    simpa using Fintype.card_subtype_compl (fun i : Fin 4 => i = j)
  let evars := Fintype.equivFinOfCardEq hcard
  let E := renameEquiv K evars
  let f := E (coordinateOneEvaluation j p)
  have hf : f ≠ 0 := by
    simpa only [map_zero] using E.injective.ne
      (coordinateOneEvaluation_ne_zero_of_homogeneous j p hp hp0)
  let eQ := Ideal.quotientEquivAlg
    (Ideal.span {coordinateOneEvaluation j p}) (Ideal.span {f}) E
    (by simp [f, Ideal.map_span])
  let eC := (chartPresentationEquiv (equationIdeal p hp) j).symm
  have eC' : ChartRing (equationIdeal p hp) j ≃+*
      (MvPolynomial (Fin 4) K ⧸ (Ideal.span {p} ⊔ coordinateOneIdeal j)) := eC
  exact ⟨f, hf, ⟨eC'.trans
    ((coordinateOneHypersurfaceQuotientEquiv j p).toRingEquiv.trans eQ.toRingEquiv)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Local dimension of a projective hypersurface chart at a maximal ideal. -/
theorem ringKrullDim_localizationAtMaximal_hypersurfaceChart_eq_two
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0) (j : Fin 4)
    (P : Ideal (ChartRing (equationIdeal p hp) j)) [P.IsMaximal] :
    ringKrullDim (Localization.AtPrime P) = 2 := by
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_hypersurfaceChart_three_variable_presentation p hp hp0 j
  let Q := P.comap e.symm
  haveI : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective e.symm e.symm.surjective
  have h := AllCharacteristics.ringKrullDim_localizationAtMaximal_polynomial_hypersurface_eq_two
    f hf Q
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
    RingEquiv.height_comap] at h
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Every closed point of a nonzero projective hypersurface in three-space has local dimension two. -/
theorem ringKrullDim_stalk_projective_hypersurface_eq_two
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0) (x : hypersurface p hp)
    (hx : IsClosed ({x} : Set (hypersurface p hp))) :
    ringKrullDim ((hypersurface p hp).presheaf.stalk x) = 2 := by
  let I := equationIdeal p hp
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart I x
  have hyclosed : IsClosed ({y} : Set (Spec (.of (ChartRing I j)))) := by
    have hpre : (chartι I j) ⁻¹' ({x} : Set (hypersurface p hp)) = {y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hy]
      exact (chartι I j).isOpenEmbedding.injective.eq_iff
    rw [← hpre]
    exact hx.preimage (chartι I j).continuous
  haveI : y.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hyclosed
  change ringKrullDim ((scheme I).presheaf.stalk x) = 2
  rw [← hy, ringKrullDim_eq_of_ringEquiv
    (asIso ((chartι I j).stalkMap y)).commRingCatIsoToRingEquiv,
    ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of (ChartRing I j)) y).commRingCatIsoToRingEquiv]
  exact ringKrullDim_localizationAtMaximal_hypersurfaceChart_eq_two p hp hp0 j y.asIdeal
end AllCharacteristics.HomogeneousProjective
