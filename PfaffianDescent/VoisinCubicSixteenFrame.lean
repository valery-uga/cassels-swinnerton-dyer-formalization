import PfaffianDescent.CubicSurfaceSectionDimensions
import PfaffianDescent.VoisinSectionRestriction

/-!
# Sixteen independent cubic sections on a cubic surface

The degree-three coordinate-ring piece has dimension nineteen.  A linear
section of the quotient map lifts sixteen of its basis elements to cubic
polynomials independent even after restriction to the surface.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero cubic surface equation admits sixteen cubic forms whose
images in its homogeneous coordinate ring are linearly independent. -/
theorem exists_cubicSixteenFrame_independent_modulo_equation
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    ∃ q : Fin 16 → homogeneousSubmodule (Fin 4) K 3,
      LinearIndependent K
        (fun i => (cubicSurfaceProjection p hp 3).rangeRestrict (q i)) := by
  let P := cubicSurfaceProjection p hp 3
  have hdim : finrank K (LinearMap.range P) = 19 := by
    rw [cubicSurfaceProjection_range]
    exact cubicSurface_grade_three_finrank p hp hne
  let b := Module.finBasisOfFinrankEq K (LinearMap.range P) hdim
  obtain ⟨s, hs⟩ := P.rangeRestrict.exists_rightInverse_of_surjective
    P.range_rangeRestrict
  let ι : Fin 16 → Fin 19 := fun i => ⟨i.1, by omega⟩
  have hι : Function.Injective ι := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin 19 => k.val) hij
  refine ⟨fun i => s (b (ι i)), ?_⟩
  have hEq : (fun i => P.rangeRestrict (s (b (ι i)))) = fun i => b (ι i) := by
    funext i
    exact DFunLike.congr_fun hs (b (ι i))
  change LinearIndependent K (fun i => P.rangeRestrict (s (b (ι i))))
  rw [hEq]
  exact b.linearIndependent.comp ι hι

/-- The chosen sixteen cubic polynomials span a space on which the
projection to cubic sections of the surface is injective. -/
theorem exists_cubicSixteenFrame_projection_injective_on_span
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    ∃ q : Fin 16 → homogeneousSubmodule (Fin 4) K 3,
      LinearIndependent K q ∧
      ∀ v ∈ Submodule.span K (Set.range q),
        cubicSurfaceProjection p hp 3 v = 0 → v = 0 := by
  obtain ⟨q, hq⟩ := exists_cubicSixteenFrame_independent_modulo_equation p hp hne
  have hq' : LinearIndependent K
      (fun i => cubicSurfaceProjection p hp 3 (q i)) := by
    exact hq.map' (LinearMap.range (cubicSurfaceProjection p hp 3)).subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hli : LinearIndependent K q := by
    exact hq'.of_comp (cubicSurfaceProjection p hp 3)
  have hdisj : Disjoint (Submodule.span K (Set.range q))
      (LinearMap.ker (cubicSurfaceProjection p hp 3)) := by
    exact Submodule.range_ker_disjoint hq'
  refine ⟨q, hli, ?_⟩
  intro v hv hzero
  have hvker : v ∈ LinearMap.ker (cubicSurfaceProjection p hp 3) := hzero
  have : v ∈ (Submodule.span K (Set.range q)) ⊓
      (LinearMap.ker (cubicSurfaceProjection p hp 3)) := ⟨hv, hvker⟩
  exact (Submodule.mem_bot K).mp (hdisj.le_bot this)

/-- The sixteen-dimensional span of the selected cubics consists of
homogeneous equations and has zero intersection with the principal ideal of
the cubic surface equation. -/
theorem exists_cubicSixteenFrame_separated_submodule
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    ∃ q : Fin 16 → homogeneousSubmodule (Fin 4) K 3,
      LinearIndependent K q ∧
      let W := Submodule.span K (Set.range (fun i => (q i).1))
      finrank K W = 16 ∧
      (∀ z ∈ W, z.IsHomogeneous 3) ∧
      (∀ z ∈ W,
        z ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → z = 0) := by
  obtain ⟨q, hli, hinj⟩ :=
    exists_cubicSixteenFrame_projection_injective_on_span p hp hne
  refine ⟨q, hli, ?_⟩
  let H := homogeneousSubmodule (Fin 4) K 3
  let W := Submodule.span K (Set.range (fun i => (q i).1))
  have hW : W = Submodule.map H.subtype (Submodule.span K (Set.range q)) := by
    simp only [W, Submodule.map_span, ← Set.range_comp']
    rfl
  have hliPoly : LinearIndependent K (fun i => (q i).1) := by
    exact hli.map' H.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hdim : finrank K W = 16 := by
    simpa only [W, Fintype.card_fin] using finrank_span_eq_card hliPoly
  refine ⟨hdim, ?_, ?_⟩
  · intro z hz
    change z ∈ W at hz
    rw [hW] at hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz
    exact v.property
  · intro z hz hzideal
    change z ∈ W at hz
    rw [hW] at hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz
    have hzero : cubicSurfaceProjection p hp 3 v = 0 := by
      change Ideal.Quotient.mk (equationIdeal p hp).toIdeal v.val = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact hzideal
    exact congrArg Subtype.val (hinj v hv hzero)

/-- Coordinates on a coefficient algebra whose sixteen labeled residue-field
evaluations detect a chosen family of cubic forms. -/
structure DetectingCubicSixteenFrameCoordinates
    (Q A L : Type u) [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (φ : Fin 16 → A →ₐ[Q] L)
    (r : Fin 16 → MvPolynomial (Fin 4) Q) where
  x : Fin 4 → A
  evalSurjective : Function.Surjective (eval₂Hom (algebraMap Q A) x)
  detects : ∀ c : Fin 16 → Q,
    (∀ i, MvPolynomial.eval₂ (algebraMap Q L)
      (fun j => φ i (x j))
      (∑ j, MvPolynomial.C (c j) * r j) = 0) → c = 0

/-- A detecting presentation whose coordinates also satisfy the defining
cubic surface equation. -/
structure DetectingCubicSixteenFrameCoordinatesOnCubic
    (Q A L : Type u) [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (p : MvPolynomial (Fin 4) Q)
    (φ : Fin 16 → A →ₐ[Q] L)
    (r : Fin 16 → MvPolynomial (Fin 4) Q) where
  data : DetectingCubicSixteenFrameCoordinates Q A L φ r
  cubicZero : p.eval₂ (algebraMap Q A) data.x = 0

/-- Detection after a field extension gives surjectivity of a sixteen-term
evaluation map into a sixteen-dimensional coefficient algebra. -/
theorem sixteen_cubicEvaluation_surjective_of_residue_detection
    {Q A L : Type u} [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L] [FiniteDimensional Q A]
    (hdim : finrank Q A = 16)
    (x : Fin 4 → A) (r : Fin 16 → MvPolynomial (Fin 4) Q)
    (φ : Fin 16 → A →ₐ[Q] L)
    (hdetect : ∀ c : Fin 16 → Q,
      (∀ i, MvPolynomial.eval₂ (algebraMap Q L)
        (fun j => φ i (x j))
        (∑ j, MvPolynomial.C (c j) * r j) = 0) → c = 0) :
    Function.Surjective
      (Fintype.linearCombination Q
        (fun j => MvPolynomial.eval₂ (algebraMap Q A) x (r j))) := by
  let E : (Fin 16 → Q) →ₗ[Q] A :=
    Fintype.linearCombination Q
      (fun j => MvPolynomial.eval₂ (algebraMap Q A) x (r j))
  have hinj : Function.Injective E := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro c hc
      apply hdetect c
      intro i
      have heval : E c = MvPolynomial.eval₂ (algebraMap Q A) x
          (∑ j, MvPolynomial.C (c j) * r j) := by
        simp [E, Fintype.linearCombination_apply, MvPolynomial.eval₂_sum,
          MvPolynomial.eval₂_mul, Algebra.smul_def]
      have hcomp := MvPolynomial.hom_eval₂
        (∑ j, MvPolynomial.C (c j) * r j)
        (algebraMap Q A) (φ i).toRingHom x
      have hmap : (φ i).toRingHom.comp (algebraMap Q A) = algebraMap Q L := by
        ext t
        exact (φ i).commutes t
      rw [hmap] at hcomp
      have hi : MvPolynomial.eval₂ (algebraMap Q L)
          (fun j => φ i (x j)) (∑ j, MvPolynomial.C (c j) * r j) =
          φ i (MvPolynomial.eval₂ (algebraMap Q A) x
            (∑ j, MvPolynomial.C (c j) * r j)) := by
        simpa using hcomp.symm
      rw [hi, ← heval, LinearMap.mem_ker.mp hc, map_zero]
    · exact bot_le
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
  simpa [E, hdim] using (Module.finrank_pi_fintype (R := Q) (ι := Fin 16) (M := fun _ => Q))

theorem DetectingCubicSixteenFrameCoordinates.frameEvaluation_surjective
    {Q A L : Type u} [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L] [FiniteDimensional Q A]
    {φ : Fin 16 → A →ₐ[Q] L}
    {r : Fin 16 → MvPolynomial (Fin 4) Q}
    (d : DetectingCubicSixteenFrameCoordinates Q A L φ r)
    (hdim : finrank Q A = 16) :
    Function.Surjective (Fintype.linearCombination Q
      (fun j => MvPolynomial.eval₂ (algebraMap Q A) d.x (r j))) :=
  sixteen_cubicEvaluation_surjective_of_residue_detection
    hdim d.x r φ d.detects

/-- A surjective evaluation map on any sixteen cubic forms makes the full
degree-three restriction map surjective. -/
theorem cubicSectionRestriction_surjective_of_frameEvaluation
    {Q A : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [FiniteDimensional Q A]
    (x : Fin 4 → A) (r : Fin 16 → MvPolynomial (Fin 4) Q)
    (hr : ∀ j, (r j).IsHomogeneous 3)
    (hsurj : Function.Surjective (Fintype.linearCombination Q
      (fun j => MvPolynomial.eval₂ (algebraMap Q A) x (r j)))) :
    Function.Surjective (homogeneousSectionRestriction (K := Q) x 3) := by
  let q : Fin 16 → homogeneousSubmodule (Fin 4) Q 3 :=
    fun j => ⟨r j, hr j⟩
  intro y
  obtain ⟨c, hc⟩ := hsurj y
  refine ⟨Fintype.linearCombination Q q c, ?_⟩
  simpa [q, homogeneousSectionRestriction_apply,
    Fintype.linearCombination_apply, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, Algebra.smul_def] using hc

/-- Sixteen independent cubic evaluation values leave exactly four cubic
equations in the kernel before quotienting by the surface equation. -/
theorem cubicSectionRestriction_kernel_finrank_eq_four_of_frameEvaluation
    {Q A : Type u} [Field Q] [CommRing A] [Algebra Q A]
    [FiniteDimensional Q A]
    (x : Fin 4 → A) (r : Fin 16 → MvPolynomial (Fin 4) Q)
    (hr : ∀ j, (r j).IsHomogeneous 3)
    (hdim : finrank Q A = 16)
    (hsurj : Function.Surjective (Fintype.linearCombination Q
      (fun j => MvPolynomial.eval₂ (algebraMap Q A) x (r j)))) :
    finrank Q (LinearMap.ker
      (homogeneousSectionRestriction (K := Q) x 3)) = 4 :=
  cubic_degree_sixteen_restriction_kernel_finrank_eq_four_of_surjective
    x hdim (cubicSectionRestriction_surjective_of_frameEvaluation x r hr hsurj)

/-- For a detecting presentation on a cubic, the vanishing system has
dimension exactly three after the defining cubic is removed. -/
theorem DetectingCubicSixteenFrameCoordinatesOnCubic.vanishingModuloCubic_finrank_eq_three
    {Q A L : Type u} [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L] [FiniteDimensional Q A]
    (p : MvPolynomial (Fin 4) Q) (hp : p.IsHomogeneous 3)
    {φ : Fin 16 → A →ₐ[Q] L}
    {r : Fin 16 → MvPolynomial (Fin 4) Q}
    (hr : ∀ j, (r j).IsHomogeneous 3)
    (d : DetectingCubicSixteenFrameCoordinatesOnCubic Q A L p φ r)
    (hA : finrank Q A = 16) :
    cubicVanishingSectionsModuloEquationFinrank p hp d.data.x d.cubicZero = 3 := by
  have hframe := d.data.frameEvaluation_surjective hA
  have hfull := cubicSectionRestriction_surjective_of_frameEvaluation
    d.data.x r hr hframe
  exact cubic_degree_sixteen_vanishing_sections_finrank_eq_three_of_surjective
    p hp d.data.x d.cubicZero hA hfull

end PfaffianDescent
