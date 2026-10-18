import AllCharacteristics.ProjectivePoints
import AllCharacteristics.GenericPointDominance
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Projective dominance from the homogeneous relations alone

A chosen coordinate tuple may have additional nonhomogeneous relations, for
example after normalization.  Projective dominance only needs that every
homogeneous relation satisfied by the tuple already belongs to the defining
homogeneous ideal.  The proof uses homogeneous numerators in the actual
degree-zero chart localization; it does not assume injectivity of the entire
homogeneous coordinate algebra into the coefficient field.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace AllCharacteristics
namespace HomogeneousProjective

universe u

variable {R L : Type u} [CommRing R] [Field L] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Detection of all homogeneous polynomial relations gives an injective
homomorphism from the actual projective chart ring.  Every prescribed
coordinate ratio and the coefficient map are retained. -/
theorem exists_injective_chart_hom_of_homogeneous_relations
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (E : MvPolynomial σ R →+* L)
    (he : ∀ p : MvPolynomial σ R, p ∈ I.toIdeal → E p = 0)
    (hdetect : ∀ (p : MvPolynomial σ R) (d : ℕ),
      p.IsHomogeneous d → E p = 0 → p ∈ I.toIdeal)
    (j : σ) (hj : E (MvPolynomial.X j) ≠ 0) :
    ∃ g : ChartRing I j →+* L,
      Function.Injective g ∧ g.comp (chartBaseMap I j) = E.comp MvPolynomial.C ∧
      ∀ i, g (chartCoordinate I j i) = E (MvPolynomial.X i) / E (MvPolynomial.X j) := by
  let e : CoordinateRing I →+* L := Ideal.Quotient.lift I.toIdeal E he
  have hgraded : ∀ (d : ℕ) (b : CoordinateRing I), b ∈ grading I d → e b = 0 → b = 0 := by
    intro d b hb hzero
    obtain ⟨p, hp, rfl⟩ := hb
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hdetect p d hp hzero
  have hej : e (coordinate I j) = E (MvPolynomial.X j) := rfl
  have hunit : IsUnit (e (coordinate I j)) :=
    isUnit_iff_ne_zero.mpr (hej.symm ▸ hj)
  let A := Localization (Submonoid.powers (coordinate I j))
  let l : A →+* L := IsLocalization.Away.lift (coordinate I j) hunit
  let g : ChartRing I j →+* L := l.comp (algebraMap (ChartRing I j) A)
  have hginj : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro a ha
    obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective (grading I) (coordinate_mem I j) a
    have hnum : e b = 0 := by
      have h := congrArg l (IsLocalization.mk'_spec A b
        (⟨coordinate I j ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (coordinate I j)))
      rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
        map_pow] at h
      change l (Localization.mk b ⟨coordinate I j ^ n, ⟨n, rfl⟩⟩) = 0 at ha
      rw [Localization.mk_eq_mk'] at ha
      rw [ha, zero_mul] at h
      exact h.symm
    have hbzero : b = 0 := hgraded n b (by simpa only [smul_eq_mul, mul_one] using hb) hnum
    apply HomogeneousLocalization.val_injective (Submonoid.powers (coordinate I j))
    rw [Away.val_mk, HomogeneousLocalization.val_zero]
    simp only [hbzero, Localization.mk_zero]
  refine ⟨g, hginj, ?_, ?_⟩
  · ext r
    change l ((chartBaseMap I j r).val) = E (MvPolynomial.C r)
    have hb : (chartBaseMap I j r).val =
        algebraMap (CoordinateRing I) A (algebraMap R (CoordinateRing I) r) :=
      GradedChart.val_baseMap (grading I) r
    rw [hb, IsLocalization.Away.lift_eq]
    rfl
  · intro i
    apply (eq_div_iff hj).mpr
    have h := congrArg l (IsLocalization.mk'_spec A (coordinate I i)
      (⟨coordinate I j, Submonoid.mem_powers (coordinate I j)⟩ :
        Submonoid.powers (coordinate I j)))
    rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at h
    change l (Localization.mk (coordinate I i)
      ⟨coordinate I j ^ 1, ⟨1, rfl⟩⟩) * e (coordinate I j) = e (coordinate I i)
    simpa only [Localization.mk_eq_mk', pow_one] using h

/-- The homogeneous-relation criterion yields a dominant actual scheme
point of the projective target, with the specified coefficient morphism. -/
theorem exists_dominant_projective_point_of_homogeneous_relations
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    [IrreducibleSpace (scheme I)]
    (E : MvPolynomial σ R →+* L)
    (he : ∀ p : MvPolynomial σ R, p ∈ I.toIdeal → E p = 0)
    (hdetect : ∀ (p : MvPolynomial σ R) (d : ℕ),
      p.IsHomogeneous d → E p = 0 → p ∈ I.toIdeal)
    (j : σ) (hj : E (MvPolynomial.X j) ≠ 0) :
    ∃ q : Spec (.of L) ⟶ scheme I,
      q ≫ toBase I = Spec.map (CommRingCat.ofHom (E.comp MvPolynomial.C)) ∧
      IsDominant q := by
  obtain ⟨g, hginj, hgbase, hgcoords⟩ :=
    exists_injective_chart_hom_of_homogeneous_relations I E he hdetect j hj
  letI : Nonempty (Spec (.of (ChartRing I j))) :=
    ⟨Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L)⟩
  letI : IsDominant (Spec.map (CommRingCat.ofHom g)) := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap g)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot g).mp hginj]
    exact bot_le
  letI : IsDominant (chartι I j) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (chartι I j)
      (chartι I j).isOpenEmbedding.isOpenMap⟩
  refine ⟨Spec.map (CommRingCat.ofHom g) ≫ chartι I j, ?_, inferInstance⟩
  rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (g.comp (chartBaseMap I j))) =
    Spec.map (CommRingCat.ofHom (E.comp MvPolynomial.C))
  exact congrArg (fun f : R →+* L => Spec.map (CommRingCat.ofHom f)) hgbase

end HomogeneousProjective
end AllCharacteristics
