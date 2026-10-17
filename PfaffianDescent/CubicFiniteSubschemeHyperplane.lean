import PfaffianDescent.CubicLinearSectionFiniteSubscheme
import PfaffianDescent.HyperplaneParametrization
import PfaffianDescent.ProjectiveFiniteFamilyHyperplane
import PfaffianDescent.TopHomogeneousProduct
import AllCharacteristics.FiniteSubschemeDatumDisjointUnion
import AllCharacteristics.DisjointFiniteSubschemeUnionCycle
import AllCharacteristics.HomogeneousFieldDescent
import AllCharacteristics.PolynomialCoordinateOne
import AllCharacteristics.SmoothHypersurfaceChartDomain
import PfaffianDescent.FiniteSchemeSmallFieldPoint
import PfaffianDescent.ProjectiveVectorIdeal
import PfaffianDescent.ProjectiveLinearChange
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Hyperplanes avoiding finite data on a cubic surface

A positive-rank finite closed subscheme of a projective cubic surface is
contained in an affine linear chart.  The complementary hyperplane is
parametrized explicitly and is disjoint from the finite datum.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite nonempty closed subscheme of a cubic surface is disjoint from an
explicit parametrized hyperplane section. -/
theorem finiteClosedImmersion_exists_avoiding_hyperplaneSection
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] (hZ : Nonempty Z) :
    ∃ (c : Fin 4 → K) (k : Fin 4), c k ≠ 0 ∧
      Disjoint (Set.range i)
        (Set.range (linearHypersurfaceSectionι (hyperplaneInclusion c k)
          (coordinateOmission k) (hyperplaneInclusion_leftInverse c k) p hp)) := by
  let f := hypersurfaceToBase p hp
  obtain ⟨z, hz, hnz⟩ := finite_scheme_projective_image_avoiding_linear
    (equationIdeal p hp) (i ≫ f) i
  obtain ⟨ell, hell, hellz⟩ := hz
  have hellspan : ell ∈ Submodule.span K (Set.range X) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact hell
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hellspan
  have hcline : homogeneousLinearForm c = ell := by
    simp only [homogeneousLinearForm, smul_eq_C_mul] at hc ⊢
    exact hc
  obtain ⟨a⟩ := hZ
  have ellne : ell ≠ 0 := by
    intro hell0
    have hz0 : z = 0 := by
      rw [← hellz, hell0]
      rfl
    have hza := hnz a
    rw [hz0] at hza
    exact hza (Submodule.zero_mem _)
  have hcne : c ≠ 0 := by
    intro hc0
    apply ellne
    rw [← hcline, hc0]
    simp [homogeneousLinearForm]
  have hcpoint : ∃ k, c k ≠ 0 := by
    by_contra h
    push Not at h
    apply hcne
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hcpoint
  refine ⟨c, k, hk, ?_⟩
  rw [Set.disjoint_left]
  rintro y ⟨a, rfl⟩ hplane
  have hmem := (linearHypersurfaceSectionι_mem_range_iff
    (hyperplaneInclusion c k) (coordinateOmission k)
    (hyperplaneInclusion_leftInverse c k) p hp (i a)).mp hplane
  have hpivot := hmem k
  rw [hyperplaneInclusion_pivot_relation c k hk, map_mul, hcline] at hpivot
  let P := (i a).asHomogeneousIdeal.toIdeal
  have hmul : Ideal.Quotient.mk (equationIdeal p hp).toIdeal (C (c k)) *
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (C ((c k)⁻¹)) *
        Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) ∈ P := by
    exact Ideal.mul_mem_left _ _ hpivot
  have hellmem : Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell ∈ P := by
    have hunit : (C (c k) : MvPolynomial (Fin 4) K) * C ((c k)⁻¹) = 1 := by
      rw [← C_mul, mul_inv_cancel₀ hk, C_1]
    have heq : Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell =
        Ideal.Quotient.mk (equationIdeal p hp).toIdeal (C (c k)) *
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (C ((c k)⁻¹)) *
            Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) := by
      rw [← map_mul, ← map_mul, ← mul_assoc, hunit, one_mul]
    rw [heq]
    exact hmul
  apply hnz a
  rw [← hellz]
  exact hellmem

/-- A positive-rank finite datum on a cubic surface is disjoint from an
explicit parametrized hyperplane section. -/
theorem finiteSubschemeDatum_exists_avoiding_hyperplaneSection
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {n : ℕ} (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n) (hn : 0 < n) :
    ∃ (c : Fin 4 → K) (k : Fin 4), c k ≠ 0 ∧
      Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D))
        (Set.range (linearHypersurfaceSectionι (hyperplaneInclusion c k)
          (coordinateOmission k) (hyperplaneInclusion_leftInverse c k) p hp)) := by
  let f := hypersurfaceToBase p hp
  let i := finiteSubschemeDatumSpecMap f D
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  haveI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  haveI : IsFinite (i ≫ f) := by
    change IsFinite (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫ f)
    infer_instance
  obtain ⟨z, hz, hnz⟩ := finite_scheme_projective_image_avoiding_linear
    (equationIdeal p hp) (i ≫ f) i
  obtain ⟨ell, hell, hellz⟩ := hz
  have hellspan : ell ∈ Submodule.span K (Set.range X) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact hell
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hellspan
  have hcline : homogeneousLinearForm c = ell := by
    simp only [homogeneousLinearForm, smul_eq_C_mul] at hc ⊢
    exact hc
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ f)
  haveI : Module.Finite K Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite (D.val.subschemeι ≫ f)
  have hdim : Module.finrank K Γ(D.val.subscheme, ⊤) = n :=
    (finiteSchemeCoefficient_finrank (D.val.subschemeι ≫ f)).trans
      ((AllCharacteristics.finiteSchemeRank_eq_finrank _).trans
        (D.property.2.2.2 (IsLocalRing.closedPoint K)))
  haveI : Nontrivial Γ(D.val.subscheme, ⊤) :=
    Module.nontrivial_of_finrank_pos (hdim.symm ▸ hn)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := Γ(D.val.subscheme, ⊤))
  let a : Spec (.of Γ(D.val.subscheme, ⊤)) := ⟨m, hm.isPrime⟩
  have ellne : ell ≠ 0 := by
    intro hell0
    have hz0 : z = 0 := by
      rw [← hellz, hell0]
      rfl
    have hza := hnz a
    rw [hz0] at hza
    exact hza (Submodule.zero_mem _)
  have hcne : c ≠ 0 := by
    intro hc0
    apply ellne
    rw [← hcline, hc0]
    simp [homogeneousLinearForm]
  have hcpoint : ∃ k, c k ≠ 0 := by
    by_contra h
    push Not at h
    apply hcne
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hcpoint
  refine ⟨c, k, hk, ?_⟩
  rw [Set.disjoint_left]
  rintro y ⟨a, rfl⟩ hplane
  have hmem := (linearHypersurfaceSectionι_mem_range_iff
    (hyperplaneInclusion c k) (coordinateOmission k)
    (hyperplaneInclusion_leftInverse c k) p hp (i a)).mp hplane
  have hpivot := hmem k
  rw [hyperplaneInclusion_pivot_relation c k hk, map_mul, hcline] at hpivot
  let P := (i a).asHomogeneousIdeal.toIdeal
  have hmul : Ideal.Quotient.mk (equationIdeal p hp).toIdeal (C (c k)) *
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (C ((c k)⁻¹)) *
        Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) ∈ P := by
    exact Ideal.mul_mem_left _ _ hpivot
  have hellmem : Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell ∈ P := by
    have hunit : (C (c k) : MvPolynomial (Fin 4) K) * C ((c k)⁻¹) = 1 := by
      rw [← C_mul, mul_inv_cancel₀ hk, C_1]
    have heq : Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell =
        Ideal.Quotient.mk (equationIdeal p hp).toIdeal (C (c k)) *
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (C ((c k)⁻¹)) *
            Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) := by
      rw [← map_mul, ← map_mul, ← mul_assoc, hunit, one_mul]
    rw [heq]
    exact hmul
  apply hnz a
  rw [← hellz]
  exact hellmem

/-- A nonzero cubic whose principal ideal is prime does not vanish identically
on a parametrized hyperplane. -/
theorem hyperplane_restriction_ne_zero_of_prime
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (c : Fin 4 → K) (k : Fin 4) (hk : c k ≠ 0) :
    rectangularSubstitution (hyperplaneInclusion c k) p ≠ 0 := by
  intro hrest
  have hdiv : homogeneousLinearForm c ∣ p := Ideal.mem_span_singleton.mp
    (mem_span_homogeneousLinearForm_of_hyperplane_restriction_eq_zero c k hk p hrest)
  obtain ⟨q, hq⟩ := hdiv
  have hhom : (homogeneousLinearForm c).IsHomogeneous 1 := by
    unfold homogeneousLinearForm
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_C_mul_X _ _
  have hform0 : homogeneousLinearForm c ≠ 0 := by
    intro hzero
    have heval := congrArg (fun r : MvPolynomial (Fin 4) K => r.eval
      (fun j => if j = k then 1 else 0)) hzero
    simp [homogeneousLinearForm] at heval
    exact hk heval
  have hq0 : q ≠ 0 := by
    intro hq0
    apply hp0
    rw [hq, hq0, mul_zero]
  have hdegrees : p.totalDegree = (homogeneousLinearForm c).totalDegree + q.totalDegree := by
    rw [hq, MvPolynomial.totalDegree_mul_of_isDomain hform0 hq0]
  have hpdeg : p.totalDegree = 3 := hp.totalDegree hp0
  have hformdeg : (homogeneousLinearForm c).totalDegree = 1 := hhom.totalDegree hform0
  have hqdeg : q.totalDegree = 2 := by omega
  have hprodmem : homogeneousLinearForm c * q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    rw [hq]
    exact Ideal.subset_span (Set.mem_singleton _)
  rcases hprime.mem_or_mem hprodmem with hform | hqmem
  · have hdiv' : p ∣ homogeneousLinearForm c := Ideal.mem_span_singleton.mp hform
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv' hform0
    omega
  · have hdiv' : p ∣ q := Ideal.mem_span_singleton.mp hqmem
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv' hq0
    omega

/-- A positive-rank finite datum on a nonzero prime cubic admits an actual
rank-three finite line section disjoint from that datum. -/
theorem exists_rankThree_finiteSubscheme_disjoint_of_prime_cubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    ∃ D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3,
      Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)) := by
  obtain ⟨c, k, hk, hdisjoint⟩ :=
    finiteSubschemeDatum_exists_avoiding_hyperplaneSection p hp D (by decide)
  exact exists_rankThree_finiteSubscheme_disjoint_of_nonzero_linearHypersurfaceSection
    (hyperplaneInclusion c k) (coordinateOmission k)
    (hyperplaneInclusion_leftInverse c k) p hp D hdisjoint
    (hyperplane_restriction_ne_zero_of_prime p hp hp0 hprime c k hk)

/-- A nonzero prime cubic admits a rank-three finite line section disjoint
from any nonempty finite closed map to the cubic. -/
theorem exists_rankThree_finiteSubscheme_disjoint_of_prime_cubic_finiteClosedImmersion
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] (hZ : Nonempty Z) :
    ∃ D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3,
      Disjoint (Set.range i)
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)) := by
  obtain ⟨c, k, hk, hdisjoint⟩ :=
    finiteClosedImmersion_exists_avoiding_hyperplaneSection p hp i hZ
  exact exists_rankThree_finiteSubscheme_disjoint_from_map_of_nonzero_linearHypersurfaceSection
    (hyperplaneInclusion c k) (coordinateOmission k)
    (hyperplaneInclusion_leftInverse c k) p hp i hdisjoint
    (hyperplane_restriction_ne_zero_of_prime p hp hp0 hprime c k hk)

/-- The two rank-three line sections that extend a degree-ten datum to a
degree-sixteen datum, together with their successive disjointness proofs. -/
structure DegreeTenRankSixteenCompletion
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) where
  first : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3
  second : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3
  disjoint_first : Disjoint (Set.range
    (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
    (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) first))
  disjoint_second : Disjoint (Set.range (disjointSpecUnionMap
    (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
    (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) first)))
    (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) second))

/-- The final degree-three section in a degree-sixteen completion is disjoint
from the original degree-ten datum. -/
theorem DegreeTenRankSixteenCompletion.disjoint_ten_second
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {hp : p.IsHomogeneous 3}
    {D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10}
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) :
    Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.second)) := by
  exact C.disjoint_second.mono
    (range_left_subset_range_disjointSpecUnionMap _ _) (by rfl)

/-- The two added degree-three sections in a degree-sixteen completion are
disjoint from one another. -/
theorem DegreeTenRankSixteenCompletion.disjoint_first_second
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {hp : p.IsHomogeneous 3}
    {D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10}
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) :
    Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.first))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.second)) := by
  exact C.disjoint_second.mono
    (range_right_subset_range_disjointSpecUnionMap _ _) (by rfl)

/-- The rank-sixteen datum represented by a degree-ten completion. -/
noncomputable def DegreeTenRankSixteenCompletion.datum
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {hp : p.IsHomogeneous 3}
    {D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10}
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 16 :=
  finiteSubschemeDatum_rankSixteenOfDegreeTenAndTwoDegreeThree
    (hypersurfaceToBase p hp) D₁₀ C.first C.second C.disjoint_first C.disjoint_second

/-- The degree-sixteen completion retains the cycle of the original
degree-ten datum and those of its two avoiding line sections. -/
theorem DegreeTenRankSixteenCompletion.datum_cycle
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {hp : p.IsHomogeneous 3}
    {D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10}
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) :
    finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.datum =
      finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₁₀ +
        finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first +
          finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second := by
  exact finiteSubschemeDatumCycle_rankSixteenOfDegreeTenAndTwoDegreeThree
    (hypersurfaceToBase p hp) D₁₀ C.first C.second C.disjoint_first C.disjoint_second

/-- The rank-sixteen datum in a degree-ten completion has exactly the three
component supports.  This is the support-level counterpart to
`datum_cycle`, and makes the retained degree-ten datum and both added line
sections available as literal sub-supports of the completed datum. -/
theorem DegreeTenRankSixteenCompletion.range_datum_eq
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {hp : p.IsHomogeneous 3}
    {D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10}
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) :
    Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.datum) =
      Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀) ∪
        Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.first) ∪
          Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.second) := by
  unfold DegreeTenRankSixteenCompletion.datum
  unfold finiteSubschemeDatum_rankSixteenOfDegreeTenAndTwoDegreeThree
  convert range_finiteSubschemeDatumSpecMap_finiteSubschemeDatumOfThreeDisjointData
    (hypersurfaceToBase p hp) D₁₀ C.first C.second C.disjoint_first C.disjoint_second using 1 <;>
      rfl

/-- A degree-ten finite datum on a nonzero prime cubic has two successively
disjoint rank-three line sections. -/
theorem nonempty_degreeTenRankSixteenCompletion_of_prime_cubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (DegreeTenRankSixteenCompletion p hp D₁₀) := by
  let f := hypersurfaceToBase p hp
  obtain ⟨D₃, h₁₂⟩ :=
    exists_rankThree_finiteSubscheme_disjoint_of_prime_cubic p hp hp0 hprime D₁₀
  let i₁ := finiteSubschemeDatumSpecMap f D₁₀
  let i₂ := finiteSubschemeDatumSpecMap f D₃
  letI : IsFinite (D₁₀.val.subschemeι ≫ f) := D₁₀.property.1
  letI : IsFinite (D₃.val.subschemeι ≫ f) := D₃.property.1
  letI := finiteSchemeCoefficientAlgebra (D₁₀.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficientAlgebra (D₃.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficient_finite (D₁₀.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficient_finite (D₃.val.subschemeι ≫ f)
  letI : IsFinite (i₁ ≫ f) := by
    dsimp [i₁, finiteSubschemeDatumSpecMap]
    rw [Category.assoc]
    infer_instance
  letI : IsFinite (i₂ ≫ f) := by
    dsimp [i₂, finiteSubschemeDatumSpecMap]
    rw [Category.assoc]
    infer_instance
  have hi₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Γ(D₁₀.val.subscheme, ⊤))) := by
    exact finiteSubschemeDatumSpecMap_toBase f D₁₀
  have hi₂ : i₂ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Γ(D₃.val.subscheme, ⊤))) := by
    exact finiteSubschemeDatumSpecMap_toBase f D₃
  let q := disjointSpecUnionMap i₁ i₂
  letI : IsClosedImmersion q := isClosedImmersion_disjointSpecUnionMap i₁ i₂ h₁₂
  have hqbase : q ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap K (Γ(D₁₀.val.subscheme, ⊤) × Γ(D₃.val.subscheme, ⊤)))) :=
    disjointSpecUnionMap_toBase f i₁ i₂ hi₁ hi₂
  letI : IsFinite (q ≫ f) := by
    rw [hqbase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hdim : Module.finrank K Γ(D₁₀.val.subscheme, ⊤) = 10 :=
    (finiteSchemeCoefficient_finrank (D₁₀.val.subschemeι ≫ f)).trans
      ((AllCharacteristics.finiteSchemeRank_eq_finrank _).trans
        (D₁₀.property.2.2.2 (IsLocalRing.closedPoint K)))
  haveI : Nontrivial Γ(D₁₀.val.subscheme, ⊤) :=
    Module.nontrivial_of_finrank_pos (hdim.symm ▸ (by decide : 0 < 10))
  haveI : Nontrivial (Γ(D₁₀.val.subscheme, ⊤) × Γ(D₃.val.subscheme, ⊤)) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal
    (α := Γ(D₁₀.val.subscheme, ⊤) × Γ(D₃.val.subscheme, ⊤))
  let a : Spec (.of (Γ(D₁₀.val.subscheme, ⊤) × Γ(D₃.val.subscheme, ⊤))) := ⟨m, hm.isPrime⟩
  obtain ⟨D₃', h₁₂₃⟩ :=
    exists_rankThree_finiteSubscheme_disjoint_of_prime_cubic_finiteClosedImmersion
      p hp hp0 hprime q ⟨a⟩
  exact ⟨⟨D₃, D₃', h₁₂, h₁₂₃⟩⟩

/-- A degree-ten finite datum on a nonzero prime cubic extends, by two
successively disjoint rank-three line sections, to a degree-sixteen datum. -/
theorem nonempty_rankSixteen_finiteSubscheme_of_prime_cubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (FiniteSubschemeDatum (hypersurfaceToBase p hp) 16) := by
  obtain ⟨C⟩ := nonempty_degreeTenRankSixteenCompletion_of_prime_cubic
    p hp hp0 hprime D₁₀
  exact ⟨C.datum⟩

/-- An irreducible cubic equation generates a prime principal ideal. -/
theorem principalIdeal_prime_of_irreducible_cubic
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : Irreducible p) :
    (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime := by
  exact Ideal.isPrime_span_singleton_of_prime hp.prime

/-- The affine origin has exactly the irrelevant ideal as its vanishing ideal.
Together with the Nullstellensatz, this identifies the algebraic obstruction
to a projective common zero of two homogeneous factors. -/
theorem vanishingIdeal_origin_eq_idealOfVars
    {K : Type u} [Field K] :
    MvPolynomial.vanishingIdeal K ({0} : Set (Fin 4 → K)) =
      MvPolynomial.idealOfVars (Fin 4) K := by
  ext p
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  change MvPolynomial.aeval (0 : Fin 4 → K) p = 0 ↔
    p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))
  rw [MvPolynomial.aeval_zero]
  constructor
  · intro hp
    rw [← Set.image_univ]
    apply MvPolynomial.mem_ideal_span_X_image.mpr
    intro m hm
    by_contra h
    push Not at h
    have hm0 : m = 0 := by
      ext i
      exact h i (Set.mem_univ _)
    rw [hm0] at hm
    rw [Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.constantCoeff_eq] at hp
    exact (MvPolynomial.mem_support_iff.mp hm) hp
  · intro hp
    rw [← Set.image_univ] at hp
    obtain h := MvPolynomial.mem_ideal_span_X_image.mp hp
    by_contra hp0
    have hsupp : (0 : Fin 4 →₀ ℕ) ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr hp0
    obtain ⟨i, -, hi⟩ := h 0 hsupp
    exact hi rfl

/-- The irrelevant ideal in a polynomial ring over a field is prime. -/
theorem idealOfVars_isPrime
    {K : Type u} [Field K] :
    (MvPolynomial.idealOfVars (Fin 4) K).IsPrime := by
  rw [← vanishingIdeal_origin_eq_idealOfVars (K := K)]
  infer_instance

/-- If the affine zero locus of an ideal over an algebraically closed field
contains only the origin, its radical is the irrelevant ideal.  The remaining
projective-intersection step will rule this out for an ideal generated by two
positive-degree factors in four variables. -/
theorem radical_eq_idealOfVars_of_zeroLocus_subset_origin
    {K : Type u} [Field K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hzero : (0 : Fin 4 → K) ∈ MvPolynomial.zeroLocus K I)
    (honly : MvPolynomial.zeroLocus K I ≤ ({0} : Set (Fin 4 → K))) :
    I.radical = MvPolynomial.idealOfVars (Fin 4) K := by
  have hEq : MvPolynomial.zeroLocus K I = ({0} : Set (Fin 4 → K)) := by
    apply Set.Subset.antisymm honly
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hzero
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) (k := K) I, hEq,
    vanishingIdeal_origin_eq_idealOfVars (K := K)]

/-- When an ideal has the irrelevant ideal as its radical, that ideal is its
unique minimal prime. -/
theorem idealOfVars_mem_minimalPrimes_of_radical_eq
    {K : Type u} [Field K] (I : Ideal (MvPolynomial (Fin 4) K))
    (hrad : I.radical = MvPolynomial.idealOfVars (Fin 4) K) :
    MvPolynomial.idealOfVars (Fin 4) K ∈ I.minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, hrad]
  letI : (MvPolynomial.idealOfVars (Fin 4) K).IsPrime := idealOfVars_isPrime
  simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]

/-- An ideal generated by two elements cannot have the irrelevant ideal as a
minimal prime of height greater than two.  This is the Krull-height half of
the projective intersection argument for two factors. -/
theorem height_idealOfVars_le_two_of_radical_eq_span_pair
    {K : Type u} [Field K] (a b : MvPolynomial (Fin 4) K)
    (hrad : (Ideal.span ({a, b} : Set (MvPolynomial (Fin 4) K))).radical =
      MvPolynomial.idealOfVars (Fin 4) K) :
    (MvPolynomial.idealOfVars (Fin 4) K).height ≤ 2 := by
  have hminimal := idealOfVars_mem_minimalPrimes_of_radical_eq
    (Ideal.span ({a, b} : Set (MvPolynomial (Fin 4) K))) hrad
  have hbound := Ideal.height_le_card_of_mem_minimalPrimes_span
    (p := MvPolynomial.idealOfVars (Fin 4) K)
    (s := ({a, b} : Set (MvPolynomial (Fin 4) K))) (by simp) hminimal
  exact hbound.trans <| by
    exact_mod_cast
      (calc
        ({a, b} : Set (MvPolynomial (Fin 4) K)).ncard ≤ ({b} : Set _).ncard + 1 :=
          Set.ncard_insert_le _ _
        _ = 2 := by simp)

private noncomputable def irrelevantIdealProjection₁ {K : Type u} [Field K] :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 3) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2]

private noncomputable def irrelevantIdealProjection₂ {K : Type u} [Field K] :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![0, 0, MvPolynomial.X 0, MvPolynomial.X 1]

private noncomputable def irrelevantIdealProjection₃ {K : Type u} [Field K] :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 1) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![0, 0, 0, MvPolynomial.X 0]

private noncomputable def irrelevantIdealProjection₄ {K : Type u} [Field K] :
    MvPolynomial (Fin 4) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) 0

private noncomputable def irrelevantIdealStep₁₂ {K : Type u} [Field K] :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1]

private noncomputable def irrelevantIdealStep₂₃ {K : Type u} [Field K] :
    MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 1) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0]

private noncomputable def irrelevantIdealStep₃₄ {K : Type u} [Field K] :
    MvPolynomial (Fin 1) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) 0

private theorem irrelevantIdealProjection₂_comp {K : Type u} [Field K] :
    irrelevantIdealProjection₂ (K := K) =
      (irrelevantIdealStep₁₂ (K := K)).comp (irrelevantIdealProjection₁ (K := K)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [irrelevantIdealProjection₁, irrelevantIdealProjection₂, irrelevantIdealStep₁₂]
  · intro i
    fin_cases i <;>
      simp [irrelevantIdealProjection₁, irrelevantIdealProjection₂, irrelevantIdealStep₁₂]

private theorem irrelevantIdealProjection₃_comp {K : Type u} [Field K] :
    irrelevantIdealProjection₃ (K := K) =
      (irrelevantIdealStep₂₃ (K := K)).comp (irrelevantIdealProjection₂ (K := K)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [irrelevantIdealProjection₂, irrelevantIdealProjection₃, irrelevantIdealStep₂₃]
  · intro i
    fin_cases i <;>
      simp [irrelevantIdealProjection₂, irrelevantIdealProjection₃, irrelevantIdealStep₂₃]

private theorem irrelevantIdealProjection₄_comp {K : Type u} [Field K] :
    irrelevantIdealProjection₄ (K := K) =
      (irrelevantIdealStep₃₄ (K := K)).comp (irrelevantIdealProjection₃ (K := K)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [irrelevantIdealProjection₃, irrelevantIdealProjection₄, irrelevantIdealStep₃₄]
  · intro i
    fin_cases i <;>
      simp [irrelevantIdealProjection₃, irrelevantIdealProjection₄, irrelevantIdealStep₃₄]

private theorem irrelevantIdeal_ker_lt_ker₁₂ {K : Type u} [Field K] :
    RingHom.ker (irrelevantIdealProjection₁ (K := K)) <
      RingHom.ker (irrelevantIdealProjection₂ (K := K)) := by
  apply lt_of_le_of_ne
  · intro p hp
    change irrelevantIdealProjection₂ (K := K) p = 0
    rw [irrelevantIdealProjection₂_comp]
    simp only [RingHom.comp_apply]
    rw [show irrelevantIdealProjection₁ (K := K) p = 0 from hp]
    exact map_zero _
  · intro h
    have hmem : MvPolynomial.X (1 : Fin 4) ∈
        RingHom.ker (irrelevantIdealProjection₂ (K := K)) := by
      change irrelevantIdealProjection₂ (K := K) (MvPolynomial.X (1 : Fin 4)) = 0
      simp [irrelevantIdealProjection₂]
    have hnot : MvPolynomial.X (1 : Fin 4) ∉
        RingHom.ker (irrelevantIdealProjection₁ (K := K)) := by
      change irrelevantIdealProjection₁ (K := K) (MvPolynomial.X (1 : Fin 4)) ≠ 0
      simp [irrelevantIdealProjection₁]
    exact hnot (h ▸ hmem)

private theorem irrelevantIdeal_ker_lt_ker₂₃ {K : Type u} [Field K] :
    RingHom.ker (irrelevantIdealProjection₂ (K := K)) <
      RingHom.ker (irrelevantIdealProjection₃ (K := K)) := by
  apply lt_of_le_of_ne
  · intro p hp
    change irrelevantIdealProjection₃ (K := K) p = 0
    rw [irrelevantIdealProjection₃_comp]
    simp only [RingHom.comp_apply]
    rw [show irrelevantIdealProjection₂ (K := K) p = 0 from hp]
    exact map_zero _
  · intro h
    have hmem : MvPolynomial.X (2 : Fin 4) ∈
        RingHom.ker (irrelevantIdealProjection₃ (K := K)) := by
      change irrelevantIdealProjection₃ (K := K) (MvPolynomial.X (2 : Fin 4)) = 0
      simp [irrelevantIdealProjection₃]
    have hnot : MvPolynomial.X (2 : Fin 4) ∉
        RingHom.ker (irrelevantIdealProjection₂ (K := K)) := by
      change irrelevantIdealProjection₂ (K := K) (MvPolynomial.X (2 : Fin 4)) ≠ 0
      simp [irrelevantIdealProjection₂]
    exact hnot (h ▸ hmem)

private theorem irrelevantIdeal_ker_lt_ker₃₄ {K : Type u} [Field K] :
    RingHom.ker (irrelevantIdealProjection₃ (K := K)) <
      RingHom.ker (irrelevantIdealProjection₄ (K := K)) := by
  apply lt_of_le_of_ne
  · intro p hp
    change irrelevantIdealProjection₄ (K := K) p = 0
    rw [irrelevantIdealProjection₄_comp]
    simp only [RingHom.comp_apply]
    rw [show irrelevantIdealProjection₃ (K := K) p = 0 from hp]
    exact map_zero _
  · intro h
    have hmem : MvPolynomial.X (3 : Fin 4) ∈
        RingHom.ker (irrelevantIdealProjection₄ (K := K)) := by
      change irrelevantIdealProjection₄ (K := K) (MvPolynomial.X (3 : Fin 4)) = 0
      simp [irrelevantIdealProjection₄]
    have hnot : MvPolynomial.X (3 : Fin 4) ∉
        RingHom.ker (irrelevantIdealProjection₃ (K := K)) := by
      change irrelevantIdealProjection₃ (K := K) (MvPolynomial.X (3 : Fin 4)) ≠ 0
      simp [irrelevantIdealProjection₃]
    exact hnot (h ▸ hmem)

private theorem irrelevantIdeal_bot_lt_ker₁ {K : Type u} [Field K] :
    (⊥ : Ideal (MvPolynomial (Fin 4) K)) <
      RingHom.ker (irrelevantIdealProjection₁ (K := K)) := by
  apply lt_of_le_of_ne bot_le
  intro h
  have hmem : MvPolynomial.X (0 : Fin 4) ∈
      RingHom.ker (irrelevantIdealProjection₁ (K := K)) := by
    change irrelevantIdealProjection₁ (K := K) (MvPolynomial.X (0 : Fin 4)) = 0
    simp [irrelevantIdealProjection₁]
  have hnot : MvPolynomial.X (0 : Fin 4) ∉
      (⊥ : Ideal (MvPolynomial (Fin 4) K)) := by simp
  exact hnot (h ▸ hmem)

private theorem irrelevantIdeal_ker₄_eq_idealOfVars {K : Type u} [Field K] :
    RingHom.ker (irrelevantIdealProjection₄ (K := K)) =
      MvPolynomial.idealOfVars (Fin 4) K := by
  rw [← vanishingIdeal_origin_eq_idealOfVars (K := K)]
  ext p
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  change MvPolynomial.eval₂ (RingHom.id K) 0 p = 0 ↔
    irrelevantIdealProjection₄ (K := K) p = 0
  rfl

/-- The irrelevant ideal of a polynomial ring in four variables over a field
has height at least four.  The proof displays the coordinate-prime chain
explicitly, avoiding a global-dimension shortcut. -/
theorem four_le_height_idealOfVars {K : Type u} [Field K] :
    (4 : ℕ∞) ≤ (MvPolynomial.idealOfVars (Fin 4) K).height := by
  let p₁ := RingHom.ker (irrelevantIdealProjection₁ (K := K))
  let p₂ := RingHom.ker (irrelevantIdealProjection₂ (K := K))
  let p₃ := RingHom.ker (irrelevantIdealProjection₃ (K := K))
  let p₄ := RingHom.ker (irrelevantIdealProjection₄ (K := K))
  letI : (⊥ : Ideal (MvPolynomial (Fin 4) K)).IsPrime := by infer_instance
  letI : p₁.IsPrime := RingHom.ker_isPrime _
  letI : p₂.IsPrime := RingHom.ker_isPrime _
  letI : p₃.IsPrime := RingHom.ker_isPrime _
  letI : p₄.IsPrime := RingHom.ker_isPrime _
  have h₀₁ : (⊥ : Ideal (MvPolynomial (Fin 4) K)) < p₁ := irrelevantIdeal_bot_lt_ker₁
  have h₁₂ : p₁ < p₂ := irrelevantIdeal_ker_lt_ker₁₂
  have h₂₃ : p₂ < p₃ := irrelevantIdeal_ker_lt_ker₂₃
  have h₃₄ : p₃ < p₄ := irrelevantIdeal_ker_lt_ker₃₄
  have h1 : (1 : ℕ∞) ≤ p₁.height := by
    simpa [Ideal.height_bot] using Ideal.height_add_one_le_of_lt_of_isPrime h₀₁
  have h2 : (2 : ℕ∞) ≤ p₂.height := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p₁.height + 1 := by simpa [add_comm] using add_le_add_left h1 1
      _ ≤ p₂.height := Ideal.height_add_one_le_of_lt_of_isPrime h₁₂
  have h3 : (3 : ℕ∞) ≤ p₃.height := by
    calc
      (3 : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ p₂.height + 1 := by simpa [add_comm] using add_le_add_left h2 1
      _ ≤ p₃.height := Ideal.height_add_one_le_of_lt_of_isPrime h₂₃
  have h4 : (4 : ℕ∞) ≤ p₄.height := by
    calc
      (4 : ℕ∞) = 3 + 1 := by norm_num
      _ ≤ p₃.height + 1 := by simpa [add_comm] using add_le_add_left h3 1
      _ ≤ p₄.height := Ideal.height_add_one_le_of_lt_of_isPrime h₃₄
  simpa only [p₄, irrelevantIdeal_ker₄_eq_idealOfVars] using h4

private noncomputable def irrelevantIdealStep₂Line {K : Type u} [Field K] :
    MvPolynomial (Fin 2) K →+* MvPolynomial Unit K :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X ()]

private theorem standardLastVectorLineHom_comp_projection₂
    {K : Type u} [Field K] :
    (vectorLineHom (![0, 0, 0, 1] : Fin 4 → K)).toRingHom =
      (irrelevantIdealStep₂Line (K := K)).comp
        (irrelevantIdealProjection₂ (K := K)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [vectorLineHom, irrelevantIdealProjection₂, irrelevantIdealStep₂Line]
  · intro i
    fin_cases i <;>
      simp [vectorLineHom_X, irrelevantIdealProjection₂, irrelevantIdealStep₂Line]

/-- The homogeneous prime ideal of the last coordinate point in projective
three-space has height at least three.  The proof exhibits a three-step chain
of coordinate-prime kernels ending in that point ideal. -/
theorem three_le_height_standardLast_vectorLineIdeal
    {K : Type u} [Field K] :
    (3 : ℕ∞) ≤
      (vectorLineIdeal (![0, 0, 0, 1] : Fin 4 → K)).toIdeal.height := by
  let p₁ := RingHom.ker (irrelevantIdealProjection₁ (K := K))
  let p₂ := RingHom.ker (irrelevantIdealProjection₂ (K := K))
  let p₃ := (vectorLineIdeal (![0, 0, 0, 1] : Fin 4 → K)).toIdeal
  letI : (⊥ : Ideal (MvPolynomial (Fin 4) K)).IsPrime := by infer_instance
  letI : p₁.IsPrime := RingHom.ker_isPrime _
  letI : p₂.IsPrime := RingHom.ker_isPrime _
  letI : p₃.IsPrime := vectorLineIdeal_prime _
  have h₀₁ : (⊥ : Ideal (MvPolynomial (Fin 4) K)) < p₁ :=
    irrelevantIdeal_bot_lt_ker₁
  have h₁₂ : p₁ < p₂ := irrelevantIdeal_ker_lt_ker₁₂
  have h₂₃ : p₂ < p₃ := by
    apply lt_of_le_of_ne
    · intro f hf
      change (vectorLineHom (![0, 0, 0, 1] : Fin 4 → K)).toRingHom f = 0
      rw [standardLastVectorLineHom_comp_projection₂, RingHom.comp_apply,
        show irrelevantIdealProjection₂ (K := K) f = 0 from hf, map_zero]
    · intro h
      have hm : X (2 : Fin 4) ∈ p₃ := by
        change vectorLineHom (![0, 0, 0, 1] : Fin 4 → K) (X 2) = 0
        simp [vectorLineHom_X]
      have hn : X (2 : Fin 4) ∉ p₂ := by
        change irrelevantIdealProjection₂ (K := K) (X 2) ≠ 0
        simp [irrelevantIdealProjection₂]
      exact hn (h ▸ hm)
  have h1 : (1 : ℕ∞) ≤ p₁.height := by
    simpa [Ideal.height_bot] using
      Ideal.height_add_one_le_of_lt_of_isPrime h₀₁
  have h2 : (2 : ℕ∞) ≤ p₂.height := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p₁.height + 1 := by simpa [add_comm] using add_le_add_left h1 1
      _ ≤ p₂.height := Ideal.height_add_one_le_of_lt_of_isPrime h₁₂
  calc
    (3 : ℕ∞) = 2 + 1 := by norm_num
    _ ≤ p₂.height + 1 := by simpa [add_comm] using add_le_add_left h2 1
    _ ≤ p₃.height := Ideal.height_add_one_le_of_lt_of_isPrime h₂₃

/-- A triangular matrix whose last column is a point normalized in the last
coordinate.  It sends the last coordinate vector to that point. -/
noncomputable def normalizedLastPointMatrix
    {K : Type u} [Field K] (x : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  fun i k ↦ if k = 3 then x i else if i = k then 1 else 0

lemma normalizedLastPointMatrix_mulVec_last
    {K : Type u} [Field K] (x : Fin 4 → K) :
    (normalizedLastPointMatrix x).mulVec (![0, 0, 0, 1] : Fin 4 → K) = x := by
  funext i
  fin_cases i <;>
    simp [normalizedLastPointMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma normalizedLastPointMatrix_mulVec_apply
    {K : Type u} [Field K] (x v : Fin 4 → K) (hx : x 3 = 1) (i : Fin 4) :
    (normalizedLastPointMatrix x).mulVec v i =
      (if i = 3 then v 3 else v i + x i * v 3) := by
  fin_cases i <;>
    simp [normalizedLastPointMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hx]

lemma normalizedLastPointMatrix_injective
    {K : Type u} [Field K] (x : Fin 4 → K) (hx : x 3 = 1) :
    Function.Injective (normalizedLastPointMatrix x).mulVec := by
  intro v w hvw
  have h3 : v 3 = w 3 := by
    have h := congrFun hvw (3 : Fin 4)
    simpa [normalizedLastPointMatrix_mulVec_apply x v hx,
      normalizedLastPointMatrix_mulVec_apply x w hx] using h
  funext i
  have hi := congrFun hvw i
  rw [normalizedLastPointMatrix_mulVec_apply x v hx i,
    normalizedLastPointMatrix_mulVec_apply x w hx i] at hi
  fin_cases i <;> simp_all

/-- Every projective point normalized in the last coordinate has homogeneous
prime ideal of height at least three. -/
theorem three_le_height_vectorLineIdeal_of_last_eq_one
    {K : Type u} [Field K] (x : Fin 4 → K) (hx : x 3 = 1) :
    (3 : ℕ∞) ≤ (vectorLineIdeal x).toIdeal.height := by
  let M := normalizedLastPointMatrix x
  have hinj : Function.Injective M.mulVec :=
    normalizedLastPointMatrix_injective x hx
  have hdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hMlast : M.mulVec (![0, 0, 0, 1] : Fin 4 → K) = x :=
    normalizedLastPointMatrix_mulVec_last x
  have hinv : M⁻¹.mulVec x = (![0, 0, 0, 1] : Fin 4 → K) := by
    apply hinj
    calc
      M.mulVec (M⁻¹.mulVec x) = (M * M⁻¹).mulVec x :=
        Matrix.mulVec_mulVec x M M⁻¹
      _ = x := by rw [M.mul_nonsing_inv hdet]; simp
      _ = M.mulVec (![0, 0, 0, 1] : Fin 4 → K) := hMlast.symm
  let E := linearSubstitutionEquiv M hdet
  have hmap : (vectorLineIdeal x).toIdeal.map E.toRingHom =
      (vectorLineIdeal (![0, 0, 0, 1] : Fin 4 → K)).toIdeal := by
    rw [show E = linearSubstitutionEquiv M hdet from rfl,
      vectorLineIdeal_linearSubstitutionEquiv M hdet x, hinv]
  have hstd := three_le_height_standardLast_vectorLineIdeal (K := K)
  rw [← hmap] at hstd
  have he : (Ideal.map E.toRingEquiv.toRingHom (vectorLineIdeal x).toIdeal).height =
      (vectorLineIdeal x).toIdeal.height := by
    change (Ideal.map E.toRingEquiv (vectorLineIdeal x).toIdeal).height = _
    exact E.toRingEquiv.height_map (vectorLineIdeal x).toIdeal
  rw [he] at hstd
  exact hstd

/-- The height-three lower bound for a projective point ideal, using any
coordinate in which its affine-cone representative is normalized. -/
theorem three_le_height_vectorLineIdeal_of_eq_one
    {K : Type u} [Field K] (x : Fin 4 → K) (j : Fin 4) (hx : x j = 1) :
    (3 : ℕ∞) ≤ (vectorLineIdeal x).toIdeal.height := by
  let e : Fin 4 ≃ Fin 4 := Equiv.swap j 3
  let y : Fin 4 → K := fun k ↦ x (e.symm k)
  have hy : y 3 = 1 := by
    change x (e.symm 3) = 1
    have he : e.symm 3 = j := by simp [e]
    rw [he, hx]
  have hyheight := three_le_height_vectorLineIdeal_of_last_eq_one y hy
  let E := MvPolynomial.renameEquiv K e
  have hmap : (vectorLineIdeal x).toIdeal.map E.toRingHom =
      (vectorLineIdeal y).toIdeal := by
    simpa [E, y] using vectorLineIdeal_renameEquiv (K := K) e x
  rw [← hmap] at hyheight
  have he : (Ideal.map E.toRingEquiv.toRingHom (vectorLineIdeal x).toIdeal).height =
      (vectorLineIdeal x).toIdeal.height := by
    change (Ideal.map E.toRingEquiv (vectorLineIdeal x).toIdeal).height = _
    exact E.toRingEquiv.height_map (vectorLineIdeal x).toIdeal
  rw [he] at hyheight
  exact hyheight

/-- A positive-degree homogeneous polynomial vanishes at the affine origin. -/
theorem aeval_zero_eq_zero_of_homogeneous_pos
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : 0 < n) :
    MvPolynomial.aeval (0 : Fin 4 → K) p = 0 := by
  rw [MvPolynomial.aeval_zero, Algebra.algebraMap_self, RingHom.id_apply,
    MvPolynomial.constantCoeff_eq]
  apply hp.coeff_eq_zero
  simpa using Ne.symm hn.ne'

/-- Two positive-degree homogeneous forms in four variables over an
algebraically closed field have a common nonzero zero.  If there were none,
their affine zero locus would be the origin; the Nullstellensatz and the
four-step coordinate-prime chain would then contradict Krull's height theorem. -/
theorem exists_nonzero_common_zero_of_homogeneous_pos
    {K : Type u} [Field K] [IsAlgClosed K]
    (a b : MvPolynomial (Fin 4) K) {m n : ℕ}
    (ha : a.IsHomogeneous m) (hb : b.IsHomogeneous n)
    (hm : 0 < m) (hn : 0 < n) :
    ∃ x : Fin 4 → K, x ≠ 0 ∧
      MvPolynomial.aeval x a = 0 ∧ MvPolynomial.aeval x b = 0 := by
  classical
  by_contra h
  have ha0 : MvPolynomial.aeval (0 : Fin 4 → K) a = 0 :=
    aeval_zero_eq_zero_of_homogeneous_pos a ha hm
  have hb0 : MvPolynomial.aeval (0 : Fin 4 → K) b = 0 :=
    aeval_zero_eq_zero_of_homogeneous_pos b hb hn
  have hzero : (0 : Fin 4 → K) ∈
      MvPolynomial.zeroLocus K (Ideal.span ({a, b} : Set (MvPolynomial (Fin 4) K))) := by
    rw [MvPolynomial.mem_zeroLocus_iff]
    let f : MvPolynomial (Fin 4) K →+* K :=
      (MvPolynomial.aeval (0 : Fin 4 → K)).toRingHom
    have hspan : Ideal.span ({a, b} : Set (MvPolynomial (Fin 4) K)) ≤ RingHom.ker f := by
      apply Ideal.span_le.2
      rintro z (rfl | rfl)
      · exact ha0
      · exact hb0
    intro p hp
    exact hspan hp
  have honly : MvPolynomial.zeroLocus K (Ideal.span ({a, b} : Set (MvPolynomial (Fin 4) K))) ≤
      ({0} : Set (Fin 4 → K)) := by
    intro x hx
    rw [Set.mem_singleton_iff]
    by_contra hx0
    have hvan := MvPolynomial.mem_zeroLocus_iff.mp hx
    have hax : MvPolynomial.aeval x a = 0 :=
      hvan a (Ideal.subset_span (by simp))
    have hbx : MvPolynomial.aeval x b = 0 :=
      hvan b (Ideal.subset_span (by simp))
    exact h ⟨x, hx0, hax, hbx⟩
  have hrad := radical_eq_idealOfVars_of_zeroLocus_subset_origin
    (I := Ideal.span ({a, b} : Set (MvPolynomial (Fin 4) K))) hzero honly
  have hle := height_idealOfVars_le_two_of_radical_eq_span_pair a b hrad
  have hge := four_le_height_idealOfVars (K := K)
  have hbad : (4 : ℕ∞) ≤ 2 := hge.trans hle
  norm_num at hbad

/-- At a common zero of two factors, every partial derivative of their
product vanishes.  This is the Jacobian calculation needed to rule out a
reducible smooth cubic once the projective intersection of the factors has
been constructed. -/
theorem pderiv_eval₂_eq_zero_of_factor_common_zero
    {R : Type u} [CommSemiring R] {L : Type v} [CommSemiring L]
    (f : R →+* L) (a b : MvPolynomial (Fin 4) R) (x : Fin 4 → L)
    (ha : a.eval₂ f x = 0) (hb : b.eval₂ f x = 0) (i : Fin 4) :
    (pderiv i (a * b)).eval₂ f x = 0 := by
  rw [pderiv_mul, eval₂_add, eval₂_mul, eval₂_mul, ha, hb]
  simp

/-- A factored hypersurface has vanishing Jacobian at every common coordinate
zero of its two displayed factors. -/
theorem pderiv_eval₂_eq_zero_of_eq_mul_and_common_zero
    {R : Type u} [CommSemiring R] {L : Type v} [CommSemiring L]
    (f : R →+* L) (p a b : MvPolynomial (Fin 4) R) (x : Fin 4 → L)
    (hfactor : p = a * b)
    (ha : a.eval₂ f x = 0) (hb : b.eval₂ f x = 0) (i : Fin 4) :
    (pderiv i p).eval₂ f x = 0 := by
  rw [hfactor]
  exact pderiv_eval₂_eq_zero_of_factor_common_zero f a b x ha hb i

/-- At a common coordinate zero of two factors, their product and all of its
partial derivatives vanish.  This is the pointwise Jacobian datum consumed
by the projective hypersurface singularity argument. -/
theorem eval₂_and_pderiv_eval₂_eq_zero_of_eq_mul_and_common_zero
    {R : Type u} [CommSemiring R] {L : Type v} [CommSemiring L]
    (f : R →+* L) (p a b : MvPolynomial (Fin 4) R) (x : Fin 4 → L)
    (hfactor : p = a * b)
    (ha : a.eval₂ f x = 0) (hb : b.eval₂ f x = 0) :
    p.eval₂ f x = 0 ∧ ∀ i : Fin 4, (pderiv i p).eval₂ f x = 0 := by
  constructor
  · rw [hfactor, eval₂_mul, ha, zero_mul]
  · exact fun i =>
      pderiv_eval₂_eq_zero_of_eq_mul_and_common_zero f p a b x hfactor ha hb i

/-- Dehomogenizing a nonzero homogeneous form on a projective coordinate
chart does not make it zero. -/
theorem coordinateOneEvaluation_ne_zero_of_homogeneous
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {d : ℕ}
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) (j : Fin 4) :
    coordinateOneEvaluation (R := K) j p ≠ 0 := by
  intro hzero
  have hmk : Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) p = 0 := by
    apply (coordinateOneQuotientEquiv (R := K) j).injective
    simpa [coordinateOneQuotientEquiv_mk] using hzero
  have hmem : p ∈ coordinateOneIdeal (R := K) j :=
    Ideal.Quotient.eq_zero_iff_mem.mp hmk
  rw [coordinateOneIdeal, Ideal.mem_span_singleton] at hmem
  exact homogeneous_not_dvd_X_sub_one hp hp0 j hmem

/-- The class of a nonzero homogeneous form is nonzero in every normalized
projective coordinate quotient. -/
theorem coordinateOneQuotient_mk_ne_zero_of_homogeneous
    {K : Type u} [Field K] {p : MvPolynomial (Fin 4) K} {d : ℕ}
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) (j : Fin 4) :
    Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) p ≠ 0 := by
  intro hzero
  apply coordinateOneEvaluation_ne_zero_of_homogeneous hp hp0 j
  rw [← coordinateOneQuotientEquiv_mk]
  rw [hzero]
  rfl

/-- Setting a projective coordinate to one and then imposing the cubic
equation gives the corresponding normalized hypersurface chart. -/
noncomputable def coordinateOneHypersurfaceChartEquiv
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (j : Fin 4) :
    ((MvPolynomial (Fin 4) K ⧸ coordinateOneIdeal j) ⧸
      Ideal.span ({Ideal.Quotient.mk (coordinateOneIdeal j) p} :
        Set (MvPolynomial (Fin 4) K ⧸ coordinateOneIdeal j))) ≃+*
      ChartRing (equationIdeal p hp) j := by
  letI : Algebra K (ChartRing (equationIdeal p hp) j) :=
    (chartBaseMap (equationIdeal p hp) j).toAlgebra
  let I : Ideal (MvPolynomial (Fin 4) K) := coordinateOneIdeal j
  let J : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {p}
  have hmap : Ideal.map (Ideal.Quotient.mk I) J =
      Ideal.span ({Ideal.Quotient.mk I p} : Set (MvPolynomial (Fin 4) K ⧸ I)) := by
    dsimp [J]
    rw [Ideal.map_span]
    simp
  have hIJ : I ⊔ J = Ideal.span (Set.range (hypersurfaceChartRelations p j)) := by
    dsimp [I, J]
    simp only [coordinateOneIdeal]
    rw [range_hypersurfaceChartRelations]
    rw [← Ideal.span_union]
    congr 1
    ext q
    simp [or_comm]
  exact
    (Ideal.quotEquivOfEq hmap.symm).trans
      ((DoubleQuot.quotQuotEquivQuotSup I J).trans
        ((Ideal.quotEquivOfEq hIJ).trans
          (hypersurfaceChartRelationsEquiv p hp j).toRingEquiv))

/-- A nonzero common zero of two homogeneous forms determines a prime on a
normalized chart that contains both dehomogenized forms.  The two classes
remain nonzero there. -/
theorem exists_normalized_common_prime_of_eval₂
    {K : Type u} [Field K] (a b : MvPolynomial (Fin 4) K) {m n : ℕ}
    (ha : a.IsHomogeneous m) (hb : b.IsHomogeneous n) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (x : Fin 4 → K) (hx : x ≠ 0)
    (hax : a.eval₂ (RingHom.id K) x = 0)
    (hbx : b.eval₂ (RingHom.id K) x = 0) :
    ∃ (j : Fin 4) (M : Ideal (MvPolynomial (Fin 4) K ⧸ coordinateOneIdeal j)),
      M.IsPrime ∧
      Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) a ≠ 0 ∧
      Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) b ≠ 0 ∧
      Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) a ∈ M ∧
      Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) b ∈ M := by
  obtain ⟨j, hxj⟩ : ∃ j : Fin 4, x j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    funext i
    exact h i
  let y : Fin 4 → K := (x j)⁻¹ • x
  have hyj : y j = 1 := by simp [y, hxj]
  let e0 : MvPolynomial (Fin 4) K →+* K :=
    MvPolynomial.eval₂Hom (RingHom.id K) y
  have hI : coordinateOneIdeal (R := K) j ≤ RingHom.ker e0 := by
    rw [coordinateOneIdeal]
    apply Ideal.span_le.mpr
    rintro q rfl
    change e0 (X j - 1) = 0
    simp [e0, hyj]
  let e : (MvPolynomial (Fin 4) K ⧸ coordinateOneIdeal j) →+* K :=
    Ideal.Quotient.lift _ e0 (fun q hq => hI hq)
  let M : Ideal (MvPolynomial (Fin 4) K ⧸ coordinateOneIdeal j) := RingHom.ker e
  have hMa : Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) a ∈ M := by
    change e (Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) a) = 0
    change e0 a = 0
    change a.eval₂ (RingHom.id K) y = 0
    rw [show y = (x j)⁻¹ • x by rfl, eval₂_homogeneous_smul a ha, hax, mul_zero]
  have hMb : Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) b ∈ M := by
    change e (Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) b) = 0
    change e0 b = 0
    change b.eval₂ (RingHom.id K) y = 0
    rw [show y = (x j)⁻¹ • x by rfl, eval₂_homogeneous_smul b hb, hbx, mul_zero]
  refine ⟨j, M, RingHom.ker_isPrime e,
    coordinateOneQuotient_mk_ne_zero_of_homogeneous ha ha0 j,
    coordinateOneQuotient_mk_ne_zero_of_homogeneous hb hb0 j, hMa, hMb⟩

/-- At a common zero of two nonzero factors, either factor stays nonzero in
the localization of the quotient by their product.  If a localized factor
vanished, clearing a denominator would make that denominator divisible by
the other factor, contradicting its nonvanishing at the chosen point. -/
theorem factor_left_ne_zero_in_localization_quotient
    {R : Type*} [CommRing R] [IsDomain R]
    (a b : R) (ha0 : a ≠ 0)
    (m : Ideal R) [m.IsPrime]
    (_ha : a ∈ m) (hb : b ∈ m)
    (I : Ideal R) (hI : I = Ideal.span ({a * b} : Set R))
    (M : Ideal (R ⧸ I)) [M.IsPrime]
    (hM : M = m.map (Ideal.Quotient.mk I)) :
    algebraMap (R ⧸ I) (Localization.AtPrime M) (Ideal.Quotient.mk I a) ≠ 0 := by
  intro hzero
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl
    (Localization.AtPrime M) (Ideal.Quotient.mk I a)).mp hzero
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective s.val
  have hnot : Ideal.Quotient.mk I r ∉ M := by
    intro hmem
    have hmem' : s.val ∈ M := by
      rw [← hr]
      exact hmem
    exact s.property hmem'
  have hmul : Ideal.Quotient.mk I (r * a) = 0 := by
    rw [map_mul, hr]
    exact hs
  have hmem : r * a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hmul
  rw [hI, Ideal.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hmem
  have hrt : r = b * t := by
    apply mul_left_cancel₀ ha0
    calc
      a * r = r * a := mul_comm _ _
      _ = (a * b) * t := ht
      _ = a * (b * t) := by ring
  apply hnot
  rw [hM, hrt]
  exact Ideal.mem_map_of_mem (Ideal.Quotient.mk I) (by
    simpa [mul_comm] using m.mul_mem_left t hb)

/-- A hypersurface quotient by a nontrivial product is not a domain at a
prime where both factors vanish. -/
theorem not_isDomain_localization_quotient_of_factor_at_common_prime
    {R : Type*} [CommRing R] [IsDomain R]
    (a b : R) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (m : Ideal R) [m.IsPrime]
    (ha : a ∈ m) (hb : b ∈ m)
    (I : Ideal R) (hI : I = Ideal.span ({a * b} : Set R))
    (M : Ideal (R ⧸ I)) [M.IsPrime]
    (hM : M = m.map (Ideal.Quotient.mk I)) :
    ¬ IsDomain (Localization.AtPrime M) := by
  intro hdomain
  letI : IsDomain (Localization.AtPrime M) := hdomain
  have hleft := factor_left_ne_zero_in_localization_quotient
    a b ha0 m ha hb I hI M hM
  have hI' : I = Ideal.span ({b * a} : Set R) := by
    simpa [mul_comm] using hI
  have hright := factor_left_ne_zero_in_localization_quotient
    b a hb0 m hb ha I hI' M hM
  apply (mul_ne_zero hleft hright)
  rw [← map_mul]
  have hp : Ideal.Quotient.mk I (a * b) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [← map_mul, hp, map_zero]

/-- A nontrivial factorization on a normalized chart of a smooth projective
hypersurface is impossible when both factors vanish at the same chart prime.
The chart equivalence transfers smoothness to a domain localization, while
the two factors give nonzero zero divisors there. -/
theorem false_of_smooth_factorization_on_chart
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) [Smooth (hypersurfaceToBase p hp)] (j : Fin 4)
    {A : Type u} [CommRing A] [IsDomain A] (a b : A)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (m : Ideal A) [m.IsPrime]
    (ha : a ∈ m) (hb : b ∈ m)
    (e : (A ⧸ Ideal.span ({a * b} : Set A)) ≃+*
      ChartRing (equationIdeal p hp) j) :
    False := by
  let I : Ideal A := Ideal.span ({a * b} : Set A)
  let M : Ideal (A ⧸ I) := m.map (Ideal.Quotient.mk I)
  letI : M.IsPrime := by
    dsimp [M]
    apply Ideal.map_isPrime_of_surjective (Ideal.Quotient.mk I).surjective
    intro x hx
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hx
    rw [hq]
    exact m.mul_mem_right q (m.mul_mem_right b ha)
  have hnot : ¬ IsDomain (Localization.AtPrime M) :=
    not_isDomain_localization_quotient_of_factor_at_common_prime
      a b ha0 hb0 m ha hb I rfl M rfl
  let e' : (A ⧸ I) ≃+* ChartRing (equationIdeal p hp) j := by
    dsimp [I]
    exact e
  have hdom : IsDomain (Localization.AtPrime M) :=
    isDomain_localization_of_ringEquiv_hypersurface_chart p hp j e' M
  exact hnot hdom

/-- A smooth projective homogeneous cubic over an algebraically closed field
is irreducible.  A hypothetical factorization has a projective common zero;
normalizing at a nonzero coordinate then contradicts the domain property of
the corresponding smooth chart local ring. -/
theorem irreducible_of_smooth_homogeneous_cubic
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Irreducible p := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · exact homogeneous_not_isUnit_of_pos_degree_of_eval_zero hp (by norm_num)
  · intro a b hfactor
    by_contra hunit
    push Not at hunit
    have ha0 : a ≠ 0 := by
      intro ha
      apply hp0
      rw [hfactor, ha, zero_mul]
    have hb0 : b ≠ 0 := by
      intro hb
      apply hp0
      rw [hfactor, hb, mul_zero]
    obtain ⟨ha, hb⟩ :=
      homogeneous_factor_of_homogeneous_product ha0 hb0 (hfactor ▸ hp)
    have hapos : 0 < a.totalDegree := by
      by_contra hnot
      have hzero : a.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hunit.1
      exact isUnit_of_homogeneous_zero (hzero ▸ ha) ha0
    have hbpos : 0 < b.totalDegree := by
      by_contra hnot
      have hzero : b.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hunit.2
      exact isUnit_of_homogeneous_zero (hzero ▸ hb) hb0
    obtain ⟨x, hx, hax, hbx⟩ :=
      exists_nonzero_common_zero_of_homogeneous_pos a b ha hb hapos hbpos
    have hax' : a.eval₂ (RingHom.id K) x = 0 := by
      simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, RingHom.id_apply] using hax
    have hbx' : b.eval₂ (RingHom.id K) x = 0 := by
      simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, RingHom.id_apply] using hbx
    obtain ⟨j, M, hMprime, ha'0, hb'0, haM, hbM⟩ :=
      exists_normalized_common_prime_of_eval₂ a b ha hb ha0 hb0 x hx hax' hbx'
    let A : Type u := MvPolynomial (Fin 4) K ⧸ coordinateOneIdeal j
    letI : IsDomain A :=
      isDomain_of_ringEquiv
        (show IsDomain (MvPolynomial {i : Fin 4 // i ≠ j} K) from inferInstance)
        (coordinateOneQuotientEquiv (R := K) j).symm.toRingEquiv
    let a' : A := Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) a
    let b' : A := Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) b
    have hproduct : Ideal.span ({a' * b'} : Set A) =
        Ideal.span ({Ideal.Quotient.mk (coordinateOneIdeal (R := K) j) p} : Set A) := by
      congr 1
      dsimp [a', b']
      rw [← map_mul, ← hfactor]
    let e : (A ⧸ Ideal.span ({a' * b'} : Set A)) ≃+*
        ChartRing (equationIdeal p hp) j := by
      exact (Ideal.quotEquivOfEq hproduct).trans
        (coordinateOneHypersurfaceChartEquiv p hp j)
    exact false_of_smooth_factorization_on_chart p hp j a' b' ha'0 hb'0 M haM hbM e

/-- Smooth projective homogeneous cubics are irreducible over every field.
After extending coefficients to an algebraic closure, a nontrivial
factorization would contradict smoothness there.  Homogeneity then reflects
the resulting unit-factor alternative to the original field. -/
theorem irreducible_of_smooth_homogeneous_cubic_of_field
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Irreducible p := by
  let L : Type u := AlgebraicClosure K
  letI : Field L := inferInstanceAs (Field (AlgebraicClosure K))
  letI : Algebra K L := inferInstanceAs (Algebra K (AlgebraicClosure K))
  letI : IsAlgClosed L := inferInstanceAs (IsAlgClosed (AlgebraicClosure K))
  have hmapinj : Function.Injective (MvPolynomial.map (algebraMap K L) :
      MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) L) :=
    MvPolynomial.map_injective (algebraMap K L)
      (FaithfulSMul.algebraMap_injective K L)
  have hpmap0 : p.map (algebraMap K L) ≠ 0 := by
    intro h
    apply hp0
    exact hmapinj (by simpa using h)
  letI : Smooth (hypersurfaceToBase (p.map (algebraMap K L))
      (hp.map (algebraMap K L))) :=
    smooth_hypersurfaceToBase_map (algebraMap K L) p hp
  have hirr : Irreducible (p.map (algebraMap K L)) :=
    irreducible_of_smooth_homogeneous_cubic (p.map (algebraMap K L))
      (hp.map (algebraMap K L)) hpmap0
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · exact homogeneous_not_isUnit_of_pos_degree_of_eval_zero hp (by norm_num)
  · intro a b hfactor
    have hmapfactor : p.map (algebraMap K L) =
        a.map (algebraMap K L) * b.map (algebraMap K L) := by
      rw [← map_mul, ← hfactor]
    by_contra hunit
    push Not at hunit
    have ha0 : a ≠ 0 := by
      intro ha
      apply hp0
      rw [hfactor, ha, zero_mul]
    have hb0 : b ≠ 0 := by
      intro hb
      apply hp0
      rw [hfactor, hb, mul_zero]
    obtain ⟨ha, hb⟩ :=
      homogeneous_factor_of_homogeneous_product ha0 hb0 (hfactor ▸ hp)
    rcases hirr.isUnit_or_isUnit hmapfactor with haunit | hbunit
    · have hapos : 0 < a.totalDegree := by
        by_contra hnot
        have hzero : a.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
        apply hunit.1
        exact isUnit_of_homogeneous_zero (hzero ▸ ha) ha0
      exact (homogeneous_not_isUnit_of_pos_degree_of_eval_zero
        (ha.map (algebraMap K L)) hapos) haunit
    · have hbpos : 0 < b.totalDegree := by
        by_contra hnot
        have hzero : b.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
        apply hunit.2
        exact isUnit_of_homogeneous_zero (hzero ▸ hb) hb0
      exact (homogeneous_not_isUnit_of_pos_degree_of_eval_zero
        (hb.map (algebraMap K L)) hbpos) hbunit

/-- A smooth projective cubic has prime equation ideal.  This is the
scheme-theoretic form of geometric irreducibility needed before choosing
Voisin's auxiliary sections. -/
theorem principalIdeal_prime_of_smooth_homogeneous_cubic
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime := by
  exact principalIdeal_prime_of_irreducible_cubic p
    (irreducible_of_smooth_homogeneous_cubic_of_field p hp hp0)

/-- The prime equation ideal of a smooth cubic persists after changing its
coefficient field.  In particular this supplies the prime-surface input on
the function field of Voisin's generic configuration space. -/
theorem principalIdeal_map_prime_of_smooth_homogeneous_cubic
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    (Ideal.span ({p.map f} : Set (MvPolynomial (Fin 4) L))).IsPrime := by
  have hpmap0 : p.map f ≠ 0 := by
    intro h
    apply hp0
    exact MvPolynomial.map_injective f (RingHom.injective f) (by simpa using h)
  letI : Smooth (hypersurfaceToBase (p.map f) (hp.map f)) :=
    smooth_hypersurfaceToBase_map f p hp
  exact principalIdeal_prime_of_smooth_homogeneous_cubic (p.map f)
    (hp.map f) hpmap0

/-- A nonempty smooth cubic with prime equation ideal is integral.  The prime
coordinate ring supplies the generic point of its projective spectrum, and
smoothness supplies reducedness through the local rings. -/
theorem isIntegral_hypersurface_of_smooth_of_principalIdeal_prime
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [Nonempty (hypersurface p hp)] [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (hypersurface p hp) := by
  let I := equationIdeal p hp
  letI : IsDomain (CoordinateRing I) := by
    change IsDomain (MvPolynomial (Fin 4) K ⧸ (Ideal.span ({p} : Set _)))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr hprime
  letI : IrreducibleSpace (hypersurface p hp) := by
    let eta : ProjectiveSpectrum (grading I) :=
      ⟨⊥, by
        rw [HomogeneousIdeal.toIdeal_bot]
        exact Ideal.isPrime_bot, by
        obtain ⟨x⟩ := (inferInstance : Nonempty (hypersurface p hp))
        change ProjectiveSpectrum (grading I) at x
        intro h
        apply x.not_irrelevant_le
        exact h.trans bot_le⟩
    change IrreducibleSpace (ProjectiveSpectrum (grading I))
    rw [irreducibleSpace_def]
    exact (show IsGenericPoint eta Set.univ from by
      rw [isGenericPoint_iff_specializes]
      intro y
      simp only [Set.mem_univ, iff_true]
      apply specializes_iff_mem_closure.mpr
      apply (ProjectiveSpectrum.le_iff_mem_closure (grading I) eta y).mp
      change (⊥ : HomogeneousIdeal (grading I)) ≤ y.asHomogeneousIdeal
      exact bot_le).isIrreducible
  letI : IsReduced (hypersurface p hp) := by
    letI : ∀ x : hypersurface p hp,
        _root_.IsReduced ((hypersurface p hp).presheaf.stalk x) := fun x => by
      letI : IsDomain ((hypersurface p hp).presheaf.stalk x) :=
        isDomain_stalk_of_smooth_toSpec_field (hypersurfaceToBase p hp) x
      letI : NoZeroDivisors ((hypersurface p hp).presheaf.stalk x) :=
        IsDomain.to_noZeroDivisors _
      exact isReduced_of_noZeroDivisors
    exact isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A hypersurface whose Jacobian is nonzero at every nonzero geometric point
cannot be the product of two positive-degree homogeneous forms.  This is the
factor-to-singularity step for a smooth projective cubic; the remaining
bridge identifies scheme-theoretic smoothness with the displayed Jacobian
condition. -/
theorem false_of_homogeneous_factorization_and_jacobian_nonsingular
    {K : Type u} [Field K] [IsAlgClosed K]
    (p a b : MvPolynomial (Fin 4) K) {m n : ℕ}
    (hfactor : p = a * b)
    (ha : a.IsHomogeneous m) (hb : b.IsHomogeneous n)
    (hm : 0 < m) (hn : 0 < n)
    (hregular : ∀ x : Fin 4 → K, x ≠ 0 → p.eval₂ (RingHom.id K) x = 0 →
      ∃ i : Fin 4, (pderiv i p).eval₂ (RingHom.id K) x ≠ 0) :
    False := by
  obtain ⟨x, hx, hax, hbx⟩ :=
    exists_nonzero_common_zero_of_homogeneous_pos a b ha hb hm hn
  have hax' : a.eval₂ (RingHom.id K) x = 0 := by
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, RingHom.id_apply] using hax
  have hbx' : b.eval₂ (RingHom.id K) x = 0 := by
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, RingHom.id_apply] using hbx
  obtain ⟨hp, hpderiv⟩ :=
    eval₂_and_pderiv_eval₂_eq_zero_of_eq_mul_and_common_zero
      (RingHom.id K) p a b x hfactor hax' hbx'
  obtain ⟨i, hi⟩ := hregular x hx hp
  exact hi (hpderiv i)

/-- A nonsingular homogeneous cubic is irreducible.  Any nontrivial
factorization has homogeneous positive-degree factors, which have a common
projective zero and hence force every partial derivative of the cubic to
vanish there. -/
theorem irreducible_of_homogeneous_jacobian_nonsingular
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hregular : ∀ x : Fin 4 → K, x ≠ 0 → p.eval₂ (RingHom.id K) x = 0 →
      ∃ i : Fin 4, (pderiv i p).eval₂ (RingHom.id K) x ≠ 0) :
    Irreducible p := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · exact homogeneous_not_isUnit_of_pos_degree_of_eval_zero hp (by norm_num)
  · intro a b hfactor
    by_contra hunit
    push Not at hunit
    have ha0 : a ≠ 0 := by
      intro ha
      apply hp0
      rw [hfactor, ha, zero_mul]
    have hb0 : b ≠ 0 := by
      intro hb
      apply hp0
      rw [hfactor, hb, mul_zero]
    obtain ⟨ha, hb⟩ :=
      homogeneous_factor_of_homogeneous_product ha0 hb0 (hfactor ▸ hp)
    have hapos : 0 < a.totalDegree := by
      by_contra hnot
      have hzero : a.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hunit.1
      exact isUnit_of_homogeneous_zero (hzero ▸ ha) ha0
    have hbpos : 0 < b.totalDegree := by
      by_contra hnot
      have hzero : b.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hunit.2
      exact isUnit_of_homogeneous_zero (hzero ▸ hb) hb0
    exact false_of_homogeneous_factorization_and_jacobian_nonsingular
      p a b hfactor ha hb hapos hbpos hregular

/-- The Jacobian nonsingularity condition supplies the prime cubic needed to
adjoin the two avoiding line sections to a degree-ten finite datum. -/
theorem nonempty_rankSixteen_finiteSubscheme_of_jacobian_nonsingular_cubic
    {K : Type u} [Field K] [Infinite K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hregular : ∀ x : Fin 4 → K, x ≠ 0 → p.eval₂ (RingHom.id K) x = 0 →
      ∃ i : Fin 4, (pderiv i p).eval₂ (RingHom.id K) x ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (FiniteSubschemeDatum (hypersurfaceToBase p hp) 16) := by
  let hirr := irreducible_of_homogeneous_jacobian_nonsingular p hp hp0 hregular
  exact nonempty_rankSixteen_finiteSubscheme_of_prime_cubic p hp hp0
    (principalIdeal_prime_of_irreducible_cubic p hirr) D₁₀

/-- A smooth cubic over an algebraically closed field supplies the prime
cubic needed to adjoin the two avoiding line sections to a degree-ten datum. -/
theorem nonempty_rankSixteen_finiteSubscheme_of_smooth_cubic
    {K : Type u} [Field K] [Infinite K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (FiniteSubschemeDatum (hypersurfaceToBase p hp) 16) := by
  let hirr := irreducible_of_smooth_homogeneous_cubic p hp hp0
  exact nonempty_rankSixteen_finiteSubscheme_of_prime_cubic p hp hp0
    (principalIdeal_prime_of_irreducible_cubic p hirr) D₁₀

/-- Every smooth projective cubic over an infinite field admits the two
avoiding line sections that enlarge a degree-ten finite datum to rank sixteen.
The primeness needed by the construction follows from smoothness after base
change to an algebraic closure. -/
theorem nonempty_rankSixteen_finiteSubscheme_of_smooth_cubic_of_field
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (FiniteSubschemeDatum (hypersurfaceToBase p hp) 16) := by
  let hirr := irreducible_of_smooth_homogeneous_cubic_of_field p hp hp0
  exact nonempty_rankSixteen_finiteSubscheme_of_prime_cubic p hp hp0
    (principalIdeal_prime_of_irreducible_cubic p hirr) D₁₀

/-- A degree-ten datum on any smooth projective cubic has the two successive
disjoint degree-three line sections used in Voisin's first residual.  Thus the
completion retains its three actual components, rather than merely asserting
existence of an unrelated rank-sixteen finite scheme. -/
theorem nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (DegreeTenRankSixteenCompletion p hp D₁₀) := by
  let hirr := irreducible_of_smooth_homogeneous_cubic_of_field p hp hp0
  exact nonempty_degreeTenRankSixteenCompletion_of_prime_cubic p hp hp0
    (principalIdeal_prime_of_irreducible_cubic p hirr) D₁₀

/-- A nonzero homogeneous cubic in at least two variables has an actual
projective point over some field extension.  The rank-three line section
provides a positive-rank finite scheme, and the small-field-point theorem
extracts a geometric point from that scheme. -/
theorem nonempty_hypersurface_of_nonzero_homogeneous_cubic_equation
    {K : Type u} [Field K] [Infinite K] {n : ℕ} (hn : 2 ≤ n)
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) :
    Nonempty (hypersurface p hp) := by
  obtain ⟨D⟩ := nonempty_rankThree_finiteSubscheme_of_nonzero_homogeneous_cubic_equation
    hn p hp hp0
  let f := hypersurfaceToBase p hp
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  have hrank : (D.val.subschemeι ≫ f).finrank
      (IsLocalRing.closedPoint K) = 3 := D.property.2.2.2 _
  obtain ⟨L, _, _, _, q, _, _⟩ :=
    finiteScheme_small_field_point (D.val.subschemeι ≫ f) (by decide) hrank
  exact ⟨D.val.subschemeι (q (IsLocalRing.closedPoint L))⟩

/-- Over an infinite field, smoothness and nonvanishing of the homogeneous
cubic equation suffice for integrality of the projective hypersurface. -/
theorem isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (hypersurface p hp) := by
  letI : Nonempty (hypersurface p hp) :=
    nonempty_hypersurface_of_nonzero_homogeneous_cubic_equation
      (by decide : 2 ≤ (4 : ℕ)) p hp hp0
  exact isIntegral_hypersurface_of_smooth_of_principalIdeal_prime p hp
    (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)

/-- An irreducible cubic with a degree-ten datum has two successive avoiding
rank-three line sections and hence an actual rank-sixteen datum. -/
theorem nonempty_rankSixteen_finiteSubscheme_of_irreducible_cubic
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hirreducible : Irreducible p)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (FiniteSubschemeDatum (hypersurfaceToBase p hp) 16) := by
  exact nonempty_rankSixteen_finiteSubscheme_of_prime_cubic p hp
    hirreducible.ne_zero (principalIdeal_prime_of_irreducible_cubic p hirreducible) D₁₀

end PfaffianDescent
