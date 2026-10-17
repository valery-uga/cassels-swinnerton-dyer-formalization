import PfaffianDescent.PolynomialProjectiveMap
import PfaffianDescent.RectangularSubstitution
import PfaffianDescent.LinearChartCoordinates
import AllCharacteristics.UniversalProjectiveIncidenceGeneric
import AllCharacteristics.ProjectiveEquationParameters
import AllCharacteristics.ProjectiveClassifyingMap

/-!
# Projective parameter spaces for homogeneous linear systems

A homogeneous polynomial substitution from the full coefficient ring to a
polynomial ring in linear-system coordinates presents a projective linear
system as a closed subspace of the projective space of all equations.  This
is the bridge needed to apply the universal projective incidence construction
to a finite-dimensional system of sections.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial

namespace PfaffianDescent

open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {K : Type u} [Field K] {σ τ : Type} [Finite σ] [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective space whose homogeneous coordinates are the chosen
coordinates of a linear system. -/
noncomputable abbrev projectiveLinearSystemParameters : Scheme.{u} :=
  scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ K))

/-- A nonzero vector of coefficients over a field extension determines a
field-valued point of the corresponding projective linear system. -/
theorem exists_projectiveLinearSystemParameter_of_nonzero_coordinates
    {L : Type u} [Field L] (f : K →+* L) {n : ℕ}
    (c : Fin n → L) (hc : c ≠ 0) :
    ∃ t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n),
      t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom f) := by
  exact point_of_coordinates
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) f c hc
    (by rintro p rfl; simp)

/-- A surjective homogeneous substitution presents a projective linear system
inside the projective parameter space of degree-`d` equations. -/
noncomputable def projectiveLinearSystemToParameters
    (g : MvPolynomial (Monomials σ d) K →ₐ[K] MvPolynomial τ K)
    (hdeg : ∀ (n : ℕ) (p : MvPolynomial (Monomials σ d) K),
      p.IsHomogeneous n → (g p).IsHomogeneous n)
    (hsurj : Function.Surjective g) :
    projectiveLinearSystemParameters (K := K) (τ := τ) ⟶
      projectiveParameters K σ d :=
  polynomialProjectiveMap (ParameterIdeal K σ d)
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ K)) g bot_le hdeg hsurj

/-- The projective linear-system map is a closed immersion. -/
instance isClosedImmersion_projectiveLinearSystemToParameters
    (g : MvPolynomial (Monomials σ d) K →ₐ[K] MvPolynomial τ K)
    (hdeg : ∀ (n : ℕ) (p : MvPolynomial (Monomials σ d) K),
      p.IsHomogeneous n → (g p).IsHomogeneous n)
    (hsurj : Function.Surjective g) :
    IsClosedImmersion (projectiveLinearSystemToParameters d g hdeg hsurj) := by
  unfold projectiveLinearSystemToParameters
  exact polynomialProjectiveMap_isClosedImmersion
    (ParameterIdeal K σ d)
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ K))
    g bot_le hdeg hsurj

/-- The embedding of a projective linear system is proper. -/
instance isProper_projectiveLinearSystemToParameters
    (g : MvPolynomial (Monomials σ d) K →ₐ[K] MvPolynomial τ K)
    (hdeg : ∀ (n : ℕ) (p : MvPolynomial (Monomials σ d) K),
      p.IsHomogeneous n → (g p).IsHomogeneous n)
    (hsurj : Function.Surjective g) :
    IsProper (projectiveLinearSystemToParameters d g hdeg hsurj) := by
  infer_instance

/-- The projective linear-system embedding remains over the original
coefficient field. -/
theorem projectiveLinearSystemToParameters_toBase
    (g : MvPolynomial (Monomials σ d) K →ₐ[K] MvPolynomial τ K)
    (hdeg : ∀ (n : ℕ) (p : MvPolynomial (Monomials σ d) K),
      p.IsHomogeneous n → (g p).IsHomogeneous n)
    (hsurj : Function.Surjective g) :
    projectiveLinearSystemToParameters d g hdeg hsurj ≫
      projectiveParametersToBase K σ d =
        toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ K)) := by
  exact polynomialProjectiveMap_toBase (ParameterIdeal K σ d)
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ K)) g bot_le hdeg hsurj

/-- A family of chosen equations in a projective linear system, viewed as a
family in the full projective parameter space. -/
noncomputable def projectiveLinearSystemParameterMap
    {B : Scheme.{u}}
    (g : MvPolynomial (Monomials σ d) K →ₐ[K] MvPolynomial τ K)
    (hdeg : ∀ (n : ℕ) (p : MvPolynomial (Monomials σ d) K),
      p.IsHomogeneous n → (g p).IsHomogeneous n)
    (hsurj : Function.Surjective g)
    (s : B ⟶ projectiveLinearSystemParameters (K := K) (τ := τ)) :
    B ⟶ projectiveParameters K σ d :=
  s ≫ projectiveLinearSystemToParameters d g hdeg hsurj

/-- Pair an ambient family with a chosen family of equations in a projective
linear system, producing the parameter map required by universal incidence. -/
noncomputable def projectiveLinearSystemIncidenceParameterMap
    {B : Scheme.{u}}
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K))
    (g : MvPolynomial (Monomials σ d) K →ₐ[K] MvPolynomial τ K)
    (hdeg : ∀ (n : ℕ) (p : MvPolynomial (Monomials σ d) K),
      p.IsHomogeneous n → (g p).IsHomogeneous n)
    (hsurj : Function.Surjective g)
    (s : B ⟶ projectiveLinearSystemParameters (K := K) (τ := τ)) :
    B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K) ⨯ projectiveParameters K σ d :=
  Limits.prod.lift a (projectiveLinearSystemParameterMap d g hdeg hsurj s)

/-- Read the degree-`d` coefficients of a homogeneous polynomial in an
enumeration of the degree-`d` monomials. -/
noncomputable def homogeneousCoefficientMap
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    homogeneousSubmodule σ K d →ₗ[K] (Fin m → K) where
  toFun q i := q.1.coeff (e i).1
  map_add' q r := by
    ext i
    simp
  map_smul' a q := by
    ext i
    simp [smul_eq_C_mul]

/-- Reconstruct a homogeneous polynomial from its degree-`d` coefficients. -/
noncomputable def homogeneousCoefficientSynthesis
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    (Fin m → K) →ₗ[K] homogeneousSubmodule σ K d where
  toFun c := ⟨∑ i, MvPolynomial.monomial (e i).1 (c i), by
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    exact MvPolynomial.isHomogeneous_monomial _ (e i).2⟩
  map_add' c c' := by
    apply Subtype.ext
    simp [Finset.sum_add_distrib]
  map_smul' a c := by
    apply Subtype.ext
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (MvPolynomial.smul_monomial a).symm

/-- Coefficient synthesis followed by coefficient extraction is the identity. -/
theorem homogeneousCoefficientMap_synthesis
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    (homogeneousCoefficientMap d e).comp
      (homogeneousCoefficientSynthesis d e) =
        (LinearMap.id : (Fin m → K) →ₗ[K] (Fin m → K)) := by
  apply LinearMap.ext
  intro c
  funext i
  change (∑ j, MvPolynomial.monomial (e j).1 (c j)).coeff (e i).1 = c i
  rw [MvPolynomial.coeff_sum]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : (e j).1 ≠ (e i).1 := by
      intro h
      exact hji (e.injective (Subtype.ext h))
    simp [hne]
  · simp

/-- Coefficient extraction followed by synthesis is the identity on the
degree-`d` homogeneous part. -/
theorem homogeneousCoefficientSynthesis_map
    {m : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : homogeneousSubmodule σ K d) :
    homogeneousCoefficientSynthesis d e
      (homogeneousCoefficientMap d e q) = q := by
  apply Subtype.ext
  dsimp [homogeneousCoefficientSynthesis, homogeneousCoefficientMap]
  calc
    ∑ i : Fin m, MvPolynomial.monomial (e i).1 (q.1.coeff (e i).1) =
        ∑ i : Monomials σ d, MvPolynomial.monomial i.1 (q.1.coeff i.1) :=
      Fintype.sum_equiv e
        (fun i : Fin m => MvPolynomial.monomial (e i).1 (q.1.coeff (e i).1))
        (fun i : Monomials σ d => MvPolynomial.monomial i.1 (q.1.coeff i.1))
        (fun _ ↦ rfl)
    _ = q.1 := AllCharacteristics.UniversalHomogeneous.sum_monomial_coeff_eq q.1 q.2

/-- The coefficient maps form mutually inverse linear equivalences between
the degree-`d` homogeneous part and its coefficient vectors. -/
theorem homogeneousCoefficientSynthesis_comp_map
    {m : ℕ} (e : Fin m ≃ Monomials σ d) :
    (homogeneousCoefficientSynthesis d e).comp
      (homogeneousCoefficientMap d e) =
        (LinearMap.id : homogeneousSubmodule σ K d →ₗ[K]
          homogeneousSubmodule σ K d) := by
  apply LinearMap.ext
  intro q
  exact homogeneousCoefficientSynthesis_map d e q

/-- The linear map determined by a finite frame of homogeneous forms. -/
noncomputable def homogeneousFrameMap
    {n : ℕ} (q : Fin n → homogeneousSubmodule σ K d) :
    (Fin n → K) →ₗ[K] homogeneousSubmodule σ K d :=
  Fintype.linearCombination K q

/-- The coefficient matrix of a finite homogeneous frame. -/
noncomputable def homogeneousFrameCoefficientMatrix
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) : Matrix (Fin m) (Fin n) K :=
  LinearMap.toMatrix' ((homogeneousCoefficientMap d e).comp
    (homogeneousFrameMap d q))

/-- The entries of the frame matrix are exactly the polynomial coefficients. -/
theorem homogeneousFrameCoefficientMatrix_apply
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) (i : Fin m) (j : Fin n) :
    homogeneousFrameCoefficientMatrix d e q i j = (q j).1.coeff (e i).1 := by
  unfold homogeneousFrameCoefficientMatrix
  rw [LinearMap.toMatrix'_apply]
  change ((Fintype.linearCombination K q) (Pi.single j 1)).1.coeff (e i).1 = _
  rw [Fintype.linearCombination_apply_single]
  simp

/-- A retraction from ambient degree-`d` coefficient vectors to the
coordinates of a homogeneous frame. -/
noncomputable def homogeneousFrameCoefficientRetraction
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) :
    (Fin m → K) →ₗ[K] (Fin n → K) :=
  (homogeneousFrameMap d q).leftInverse.comp
    (homogeneousCoefficientSynthesis d e)

/-- Matrix form of the frame-coordinate retraction. -/
noncomputable def homogeneousFrameCoefficientRetractionMatrix
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) : Matrix (Fin n) (Fin m) K :=
  LinearMap.toMatrix' (homogeneousFrameCoefficientRetraction d e q)

/-- An independent homogeneous frame has a split coefficient matrix. -/
theorem homogeneousFrameCoefficientMatrix_has_retraction
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q) :
    homogeneousFrameCoefficientRetractionMatrix d e q *
      homogeneousFrameCoefficientMatrix d e q = 1 := by
  have hker : LinearMap.ker (homogeneousFrameMap d q) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hqli.fintypeLinearCombination_injective
  have hcomp : (homogeneousFrameCoefficientRetraction d e q).comp
      ((homogeneousCoefficientMap d e).comp
        (homogeneousFrameMap d q)) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (homogeneousFrameMap d q).leftInverse
      (homogeneousCoefficientSynthesis d e
        (homogeneousCoefficientMap d e (homogeneousFrameMap d q x))) = x
    rw [homogeneousCoefficientSynthesis_map]
    exact LinearMap.leftInverse_apply_of_inj hker x
  change LinearMap.toMatrix' (homogeneousFrameCoefficientRetraction d e q) *
    LinearMap.toMatrix' ((homogeneousCoefficientMap d e).comp
      (homogeneousFrameMap d q)) = 1
  rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id]

/-- A nonzero coefficient vector over any field extension gives a nonzero
linear combination of an independent homogeneous frame. -/
theorem homogeneousFrameCombination_map_ne_zero_of_ne_zero
    {m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q) (c : Fin n → L) (hc : c ≠ 0) :
    ∑ j, MvPolynomial.C (c j) * (q j).1.map f ≠ 0 := by
  classical
  let M := homogeneousFrameCoefficientMatrix d e q
  let N := homogeneousFrameCoefficientRetractionMatrix d e q
  have hNM : N * M = 1 := homogeneousFrameCoefficientMatrix_has_retraction d e q hqli
  have hNMmap : (N.map f) * (M.map f) = 1 := by
    rw [← Matrix.map_mul]
    simpa using congrArg (fun X => X.map f) hNM
  have hMinj : Function.Injective (M.map f).mulVec := by
    intro x y hxy
    have h := congrArg (fun z => (N.map f).mulVec z) hxy
    calc
      x = ((N.map f) * (M.map f)).mulVec x := by rw [hNMmap, Matrix.one_mulVec]
      _ = (N.map f).mulVec ((M.map f).mulVec x) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = (N.map f).mulVec ((M.map f).mulVec y) := h
      _ = ((N.map f) * (M.map f)).mulVec y := Matrix.mulVec_mulVec _ _ _
      _ = y := by rw [hNMmap, Matrix.one_mulVec]
  intro hsum
  apply hc
  apply hMinj
  have hcoeff : (M.map f).mulVec c = 0 := by
    funext i
    change (∑ j, f (M i j) * c j) = 0
    rw [show (∑ j, f (M i j) * c j) =
      (∑ j, MvPolynomial.C (c j) * (q j).1.map f).coeff (e i).1 by
        rw [MvPolynomial.coeff_sum]
        apply Finset.sum_congr rfl
        intro j _
        change f (homogeneousFrameCoefficientMatrix d e q i j) * c j = _
        rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
          homogeneousFrameCoefficientMatrix_apply]
        exact mul_comm _ _]
    rw [hsum, MvPolynomial.coeff_zero]
  simpa using hcoeff

/-- The degree-`d` coefficients of a frame combination are the matrix product
of the frame coefficient matrix with its coordinate vector. -/
theorem homogeneousFrameCombination_map_coeff
    {m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (c : Fin n → L) (i : Fin m) :
    (∑ j, MvPolynomial.C (c j) * (q j).1.map f).coeff (e i).1 =
      ((homogeneousFrameCoefficientMatrix d e q).map f).mulVec c i := by
  change (∑ j, MvPolynomial.C (c j) * (q j).1.map f).coeff (e i).1 =
    ∑ j, f (homogeneousFrameCoefficientMatrix d e q i j) * c j
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
    homogeneousFrameCoefficientMatrix_apply]
  exact mul_comm _ _

/-- The homogeneous substitution attached to a matrix of coefficients for a
linear system.  The equivalence identifies the degree-`d` monomials with the
rows of the coefficient matrix. -/
noncomputable def projectiveLinearSystemMatrixSubstitution
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) :
    MvPolynomial (Monomials σ d) K →ₐ[K] MvPolynomial (Fin n) K :=
  (rectangularSubstitution M).comp (MvPolynomial.rename e.symm)

/-- A target coefficient coordinate pulls back to the corresponding linear
form in the coordinates of the projective linear system. -/
theorem projectiveLinearSystemMatrixSubstitution_X
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    projectiveLinearSystemMatrixSubstitution d e M (MvPolynomial.X (e i)) =
      rectangularLinearCoordinate M i := by
  unfold projectiveLinearSystemMatrixSubstitution
  rw [AlgHom.comp_apply, MvPolynomial.rename_X, rectangularSubstitution_X]
  simp

/-- On every affine chart of a projective linear-system parameter space, a
target coefficient ratio evaluates to the corresponding row of the defining
matrix applied to the normalized source coordinates. -/
theorem normalized_rectangularLinearCoordinate_apply
    {m n : ℕ} {L : Type u} [Field L]
    (M : Matrix (Fin m) (Fin n) K) (i : Fin m)
    (z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) z →+* L)
    (f : K →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap
      (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := z)) = f) :
    g (AllCharacteristics.GradedChart.normalized
      (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) hz
      (Ideal.Quotient.mk ((⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)).toIdeal)
        (rectangularLinearCoordinate M i))
      (by
        simpa using (polynomial_class_mem_grading
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
          (rectangularLinearCoordinate M i)
          (rectangularLinearCoordinate_homogeneous M i)))) =
      (M.map f).mulVec (fun j => g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) z hz j)) i := by
  rw [AllCharacteristics.GradedChart.normalized]
  rw [← eval₂_linearChartCoordinate_eq_fraction
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) z hz
    (rectangularLinearCoordinate M i) (rectangularLinearCoordinate_homogeneous M i)]
  rw [MvPolynomial.hom_eval₂, hbase]
  exact eval₂_rectangularLinearCoordinate M i f _

/-- The preceding chart formula applies to any degree-one coordinate once it
is identified with the relevant matrix-defined linear form. -/
theorem normalized_coordinate_apply_of_eq
    {m n : ℕ} {L : Type u} [Field L]
    (M : Matrix (Fin m) (Fin n) K) (i : Fin m)
    (z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) z →+* L)
    (f : K →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap
      (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := z)) = f)
    (w : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hw : w ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (hwM : w = Ideal.Quotient.mk
      ((⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)).toIdeal)
      (rectangularLinearCoordinate M i)) :
    g (AllCharacteristics.GradedChart.normalized
      (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) hz w hw) =
      (M.map f).mulVec (fun j => g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) z hz j)) i := by
  subst w
  exact normalized_rectangularLinearCoordinate_apply M i z hz g f hbase

/-- Matrix substitutions preserve the ordinary homogeneous degree. -/
theorem projectiveLinearSystemMatrixSubstitution_homogeneous
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K)
    (r : ℕ) (p : MvPolynomial (Monomials σ d) K)
    (hp : p.IsHomogeneous r) :
    (projectiveLinearSystemMatrixSubstitution d e M p).IsHomogeneous r := by
  exact rectangularSubstitution_homogeneous M hp.rename_isHomogeneous

/-- Under the projective linear-system substitution, a coefficient coordinate
becomes the quotient class of its corresponding matrix-defined linear form. -/
theorem projectiveLinearSystemMatrix_gradingMap_coordinate
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
      (coordinate (ParameterIdeal K σ d) (e i)) =
    Ideal.Quotient.mk ((⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)).toIdeal)
      (rectangularLinearCoordinate M i) := by
  change polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
      (Ideal.Quotient.mk (ParameterIdeal K σ d).toIdeal (MvPolynomial.X (e i))) = _
  rw [polynomialQuotientGradingMap_mk,
    projectiveLinearSystemMatrixSubstitution_X]

/-- For a split matrix linear system, the pullbacks of the target coefficient
coordinates generate the irrelevant ideal of the source projective space. -/
theorem projectiveLinearSystemMatrix_coordinate_span_irrelevant
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin m) K)
    (hNM : N * M = 1) :
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    (HomogeneousIdeal.irrelevant
      (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))).toIdeal ≤
      Ideal.span (Set.range fun i : Fin m => F (coordinate (ParameterIdeal K σ d) (e i))) := by
  dsimp
  change (HomogeneousIdeal.irrelevant
    (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))).toIdeal ≤ _
  rw [irrelevant_eq_coordinateIdeal]
  apply Ideal.span_le.mpr
  rintro x ⟨j, rfl⟩
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let F := polynomialQuotientGradingMap (ParameterIdeal K σ d) I
    (projectiveLinearSystemMatrixSubstitution d e M) bot_le
    (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
  have hsub : rectangularSubstitution M (rectangularLinearCoordinate N j) =
      MvPolynomial.X j := by
    rw [rectangularSubstitution_coordinate, hNM]
    change ((1 : Matrix (Fin n) (Fin n) K).map MvPolynomial.C).mulVec MvPolynomial.X j = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hquot : Ideal.Quotient.mk I.toIdeal (MvPolynomial.X j) =
      ∑ i, algebraMap K (CoordinateRing I) (N j i) *
        Ideal.Quotient.mk I.toIdeal (rectangularLinearCoordinate M i) := by
    rw [← hsub]
    rw [show rectangularLinearCoordinate N j = ∑ i, MvPolynomial.C (N j i) * MvPolynomial.X i by
      rfl, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, rectangularSubstitution_X, map_mul]
    change Ideal.Quotient.mk I.toIdeal
      (rectangularSubstitution M (MvPolynomial.C (N j i))) * _ = _
    have hC : rectangularSubstitution M (MvPolynomial.C (N j i)) =
        MvPolynomial.C (N j i) := by
      change rectangularSubstitution M
        (algebraMap K (MvPolynomial (Fin m) K) (N j i)) =
          algebraMap K (MvPolynomial (Fin n) K) (N j i)
      exact (rectangularSubstitution M).commutes _
    rw [hC]
    rfl
  rw [show coordinate I j = Ideal.Quotient.mk I.toIdeal (MvPolynomial.X j) by rfl, hquot]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Ideal.subset_span
  refine ⟨i, ?_⟩
  simpa only [F, I] using projectiveLinearSystemMatrix_gradingMap_coordinate d e M i

/-- The target coefficient charts pull back to an affine open cover of the
projective parameter space of a split matrix linear system. -/
noncomputable def projectiveLinearSystemMatrix_coefficientAffineCover
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin m) K)
    (hNM : N * M = 1) :
    (Proj (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))).AffineOpenCover :=
  let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    (projectiveLinearSystemMatrixSubstitution d e M) bot_le
    (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
  Proj.affineOpenCoverOfIrrelevantLESpan
    (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (fun i : Fin m => F (coordinate (ParameterIdeal K σ d) (e i)))
    (fun i => F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
    (fun _ => by decide)
    (projectiveLinearSystemMatrix_coordinate_span_irrelevant d e M N hNM)

/-- Every field-valued point of a split projective linear system lies on the
pullback of some target coefficient chart. -/
theorem exists_projectiveLinearSystemMatrix_coefficient_chart
    {m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin m) K)
    (hNM : N * M = 1)
    (t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f)) :
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    ∃ i : Fin m, ∃ g : Away (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K σ d) (e i))) →+* L,
      g.comp (AllCharacteristics.GradedChart.baseMap (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (z := F (coordinate (ParameterIdeal K σ d) (e i)))) = f ∧
      Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          (F (coordinate (ParameterIdeal K σ d) (e i)))
          (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
          (by decide : 0 < 1) = t := by
  dsimp
  let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    (projectiveLinearSystemMatrixSubstitution d e M) bot_le
    (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
  let t' : Spec (.of L) ⟶
      Proj (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) := t
  have ht' : t' ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f) := ht
  let i : Fin m := (projectiveLinearSystemMatrix_coefficientAffineCover d e M N hNM).idx
    (t' (IsLocalRing.closedPoint L))
  have hcov := (projectiveLinearSystemMatrix_coefficientAffineCover d e M N hNM).covers
    (t' (IsLocalRing.closedPoint L))
  change t' (IsLocalRing.closedPoint L) ∈ Set.range
    (Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
      (F (coordinate (ParameterIdeal K σ d) (e i)))
      (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
      (by decide : 0 < 1)) at hcov
  have htrange : Set.range t' ⊆ Set.range
      (Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K σ d) (e i)))
        (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
        (by decide : 0 < 1)) := by
    rintro x ⟨v, rfl⟩
    have hv : v = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    subst v
    exact hcov
  let u : Spec (.of L) ⟶ Spec (.of (Away (grading
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
      (F (coordinate (ParameterIdeal K σ d) (e i))))) :=
    IsOpenImmersion.lift
      (Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K σ d) (e i)))
        (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
        (by decide : 0 < 1)) t' htrange
  let g := (Spec.preimage u).hom
  have hu : u ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (z := F (coordinate (ParameterIdeal K σ d) (e i))))) =
      Spec.map (CommRingCat.ofHom f) := by
    have hchartBase := homogeneousChart_toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (F (coordinate (ParameterIdeal K σ d) (e i)))
      (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))) (by decide : 0 < 1)
    calc
      u ≫ Spec.map (CommRingCat.ofHom
          (AllCharacteristics.GradedChart.baseMap (grading
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
            (z := F (coordinate (ParameterIdeal K σ d) (e i))))) =
          u ≫ (Proj.awayι (grading
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
            (F (coordinate (ParameterIdeal K σ d) (e i)))
            (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
            (by decide : 0 < 1) ≫
              toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) := by
            rw [hchartBase]
      _ = (u ≫ Proj.awayι (grading
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
            (F (coordinate (ParameterIdeal K σ d) (e i)))
            (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
            (by decide : 0 < 1)) ≫
              toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) := by
            exact (Category.assoc _ _ _).symm
      _ = t' ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) := by
            rw [IsOpenImmersion.lift_fac]
      _ = Spec.map (CommRingCat.ofHom f) := ht'
  have hg : Spec.map (CommRingCat.ofHom g) = u := Spec.map_preimage u
  refine ⟨i, g, ?_, ?_⟩
  · have hhom : CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          (z := F (coordinate (ParameterIdeal K σ d) (e i)))) ≫
        CommRingCat.ofHom g = CommRingCat.ofHom f := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg]
      exact hu
    exact congrArg CommRingCat.Hom.hom hhom
  · change Spec.map (CommRingCat.ofHom g) ≫
      Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K σ d) (e i)))
        (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
        (by decide : 0 < 1) = t'
    rw [hg]
    exact IsOpenImmersion.lift_fac _ _ _

/-- A field-valued point on a chart of a matrix-defined projective linear
system sends every target coefficient ratio to the corresponding coordinate of
the matrix-vector product of its normalized source coordinates. -/
theorem projectiveLinearSystemMatrix_awayMap_chartCoordinate_apply
    {m n : ℕ} {L : Type u} [Field L]
    (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (i k : Fin m) :
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    let s := F (coordinate (ParameterIdeal K σ d) (e i))
    let hs := F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
    ∀ (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) s →+* L)
      (f : K →+* L),
      g.comp (AllCharacteristics.GradedChart.baseMap
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := s)) = f →
      g (Away.map F (coordinate (ParameterIdeal K σ d) (e i))
        (chartCoordinate (ParameterIdeal K σ d) (e i) (e k))) =
      (M.map f).mulVec (fun j => g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)) k := by
  dsimp
  intro g f hbase
  rw [show chartCoordinate (ParameterIdeal K σ d) (e i) (e k) =
      AllCharacteristics.GradedChart.normalized (grading (ParameterIdeal K σ d))
        (coordinate_mem (ParameterIdeal K σ d) (e i))
        (coordinate (ParameterIdeal K σ d) (e k))
        (coordinate_mem (ParameterIdeal K σ d) (e k)) by rfl]
  rw [awayMap_polynomialProjectiveMap_normalized
    (ParameterIdeal K σ d)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    (projectiveLinearSystemMatrixSubstitution d e M) bot_le
    (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    (coordinate (ParameterIdeal K σ d) (e i))
    (coordinate (ParameterIdeal K σ d) (e k))
    (coordinate_mem (ParameterIdeal K σ d) (e i))
    (coordinate_mem (ParameterIdeal K σ d) (e k))]
  apply normalized_coordinate_apply_of_eq M k _ _ g f hbase
  exact projectiveLinearSystemMatrix_gradingMap_coordinate d e M k

/-- For a homogeneous frame, the projective chart coordinates of its image
are precisely the coefficients of the specialized frame combination. -/
theorem homogeneousFrame_awayMap_chartCoordinate_apply
    {m n : ℕ} {L : Type u} [Field L]
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) (i k : Fin m) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    let s := F (coordinate (ParameterIdeal K σ d) (e i))
    let hs := F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
    ∀ (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) s →+* L)
      (f : K →+* L),
      g.comp (AllCharacteristics.GradedChart.baseMap
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := s)) = f →
      g (Away.map F (coordinate (ParameterIdeal K σ d) (e i))
        (chartCoordinate (ParameterIdeal K σ d) (e i) (e k))) =
      (∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)) *
        (q j).1.map f).coeff (e k).1 := by
  dsimp
  intro g f hbase
  calc
    _ = ((homogeneousFrameCoefficientMatrix d e q).map f).mulVec
        (fun j => g (linearChartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) _ _ j)) k :=
      projectiveLinearSystemMatrix_awayMap_chartCoordinate_apply
        d e (homogeneousFrameCoefficientMatrix d e q) i k g f hbase
    _ = _ := (homogeneousFrameCombination_map_coeff d f e q _ k).symm

/-- The normalized coordinate vector of a field-valued source chart is
nonzero when the chart is pulled back from a target coefficient chart. -/
theorem homogeneousFrame_awayMap_normalizedCoordinates_ne_zero
    {m n : ℕ} {L : Type u} [Field L]
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) (i : Fin m) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    let s := F (coordinate (ParameterIdeal K σ d) (e i))
    let hs := F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
    ∀ (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) s →+* L)
      (f : K →+* L),
      g.comp (AllCharacteristics.GradedChart.baseMap
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := s)) = f →
      (fun j => g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)) ≠ 0 := by
  dsimp
  intro g f hbase hc
  have h := homogeneousFrame_awayMap_chartCoordinate_apply d e q i i g f hbase
  rw [chartCoordinate_self, map_one] at h
  have hcj : ∀ j, g (linearChartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) _ _ j) = 0 :=
    fun j => congrFun hc j
  simp_rw [hcj] at h
  simp at h

/-- For an independent homogeneous frame, the equation represented by every
field-valued chart point of its projective image is nonzero. -/
theorem homogeneousFrame_awayMap_combination_ne_zero
    {m n : ℕ} {L : Type u} [Field L]
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q) (i : Fin m) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    let s := F (coordinate (ParameterIdeal K σ d) (e i))
    let hs := F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
    ∀ (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) s →+* L)
      (f : K →+* L),
      g.comp (AllCharacteristics.GradedChart.baseMap
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := s)) = f →
      ∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)) *
        (q j).1.map f ≠ 0 := by
  dsimp
  intro g f hbase
  apply homogeneousFrameCombination_map_ne_zero_of_ne_zero d f e q hqli
  exact homogeneousFrame_awayMap_normalizedCoordinates_ne_zero d e q i g f hbase

/-- The normalized universal equation on a target coefficient chart pulls
back to the actual nonzero frame combination represented by a field-valued
source-chart point. -/
theorem map_normalizedForm_homogeneousFrame_awayMap
    {m n : ℕ} {L : Type u} [Field L]
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) (i : Fin m) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    let s := F (coordinate (ParameterIdeal K σ d) (e i))
    let hs := F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
    ∀ (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) s →+* L)
      (f : K →+* L),
      g.comp (AllCharacteristics.GradedChart.baseMap
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := s)) = f →
      (normalizedForm K σ d (e i)).map
        (g.comp (Away.map F (coordinate (ParameterIdeal K σ d) (e i))) ) =
      ∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)) *
        (q j).1.map f := by
  dsimp
  intro g f hbase
  apply map_normalizedForm_eq (e i) _ _
  · apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map f).C_mul _
  · intro a
    simpa only [RingHom.comp_apply, e.apply_symm_apply] using
      (homogeneousFrame_awayMap_chartCoordinate_apply d e q i (e.symm a) g f hbase)

/-- The target coefficient-chart homomorphism induced by a field-valued frame
point is exactly the normalized chart homomorphism of its specialized frame
combination. -/
theorem homogeneousFrame_awayMap_eq_projectiveEquationChartMap
    {m n : ℕ} {L : Type u} [Field L]
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) (i : Fin m) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    let s := F (coordinate (ParameterIdeal K σ d) (e i))
    let hs := F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
    ∀ (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) s →+* L)
      (f : K →+* L),
      g.comp (AllCharacteristics.GradedChart.baseMap
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := s)) = f →
      let p := ∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)) *
        (q j).1.map f
      ∃ hi : p.coeff (e i).1 ≠ 0,
        projectiveEquationChartMap f p (e i) hi =
          g.comp (Away.map F (coordinate (ParameterIdeal K σ d) (e i))) := by
  dsimp
  intro g f hbase
  let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    (projectiveLinearSystemMatrixSubstitution d e
      (homogeneousFrameCoefficientMatrix d e q)) bot_le
    (projectiveLinearSystemMatrixSubstitution_homogeneous d e
      (homogeneousFrameCoefficientMatrix d e q))
  let s := F (coordinate (ParameterIdeal K σ d) (e i))
  let hs : s ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1 :=
    F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
  let c : Fin n → L := fun j => g (linearChartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)
  let p := ∑ j, MvPolynomial.C (c j) * (q j).1.map f
  change ∃ hi : p.coeff (e i).1 ≠ 0,
    projectiveEquationChartMap f p (e i) hi =
      g.comp (Away.map F (coordinate (ParameterIdeal K σ d) (e i)))
  have hcoeff : p.coeff (e i).1 = 1 := by
    have h := homogeneousFrame_awayMap_chartCoordinate_apply d e q i i g f hbase
    rw [chartCoordinate_self, map_one] at h
    simpa only [F, s, hs, c, p, map_one] using h.symm
  have hi : p.coeff (e i).1 ≠ 0 := by rw [hcoeff]; exact one_ne_zero
  refine ⟨hi, ?_⟩
  apply projectiveChartMap_ext (e i)
  · apply RingHom.ext
    intro r
    change projectiveEquationChartMap f p (e i) hi
        (chartBaseMap (ParameterIdeal K σ d) (e i) r) =
      g (Away.map F (coordinate (ParameterIdeal K σ d) (e i))
        (chartBaseMap (ParameterIdeal K σ d) (e i) r))
    rw [projectiveEquationChartMap_baseMap]
    change f r = g (Away.map F _ (chartBaseMap (ParameterIdeal K σ d) (e i) r))
    have hF := polynomialQuotientGradingMap_away_base
      (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q))
      (coordinate (ParameterIdeal K σ d) (e i))
    have hFr := DFunLike.congr_fun hF r
    change Away.map F (coordinate (ParameterIdeal K σ d) (e i))
      (chartBaseMap (ParameterIdeal K σ d) (e i) r) =
        AllCharacteristics.GradedChart.baseMap
          (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) r at hFr
    calc
      f r = g (AllCharacteristics.GradedChart.baseMap
          (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) r) :=
        (DFunLike.congr_fun hbase r).symm
      _ = g (Away.map F (coordinate (ParameterIdeal K σ d) (e i))
          (chartBaseMap (ParameterIdeal K σ d) (e i) r)) := congrArg g hFr.symm
  · intro a
    rw [projectiveEquationChartMap_coordinate, hcoeff]
    simp only [inv_one, one_mul]
    simpa only [F, s, hs, c, p, RingHom.comp_apply, e.apply_symm_apply] using
      (homogeneousFrame_awayMap_chartCoordinate_apply d e q i (e.symm a) g f hbase).symm

/-- Restricting the universal degree-`d` equation to the projective parameter
space of a homogeneous frame gives the universal linear combination of that
frame. -/
theorem map_form_projectiveLinearSystemMatrixSubstitution_homogeneousFrame
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) :
    (form σ d K).map
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) =
      ∑ j, MvPolynomial.C (MvPolynomial.X j) * (q j).1.map MvPolynomial.C := by
  classical
  let P : MvPolynomial σ (MvPolynomial (Fin n) K) :=
    ∑ j, MvPolynomial.C (MvPolynomial.X j) * (q j).1.map MvPolynomial.C
  have hP : P.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map MvPolynomial.C).C_mul _
  have hsubstitution :
      projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q) =
      MvPolynomial.eval₂Hom MvPolynomial.C (fun a : Monomials σ d => P.coeff a.1) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [projectiveLinearSystemMatrixSubstitution]
    · intro a
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      change rectangularSubstitution (homogeneousFrameCoefficientMatrix d e q)
        (MvPolynomial.rename e.symm (MvPolynomial.X a)) = P.coeff a.1
      rw [MvPolynomial.rename_X, rectangularSubstitution_X]
      change (∑ j, MvPolynomial.C
        (homogeneousFrameCoefficientMatrix d e q (e.symm a) j) * MvPolynomial.X j) =
        P.coeff a.1
      rw [show P = ∑ j, MvPolynomial.C (MvPolynomial.X j) *
          (q j).1.map MvPolynomial.C by rfl,
        MvPolynomial.coeff_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
        homogeneousFrameCoefficientMatrix_apply]
      rw [e.apply_symm_apply a]
      exact mul_comm (MvPolynomial.C ((q j).1.coeff a.1)) (MvPolynomial.X j)
  rw [hsubstitution]
  exact map_form_eq MvPolynomial.C P hP

/-- After a field-valued specialization of the frame coordinates, the
restricted universal equation is the corresponding linear combination of
the frame over that field. -/
theorem map_map_form_projectiveLinearSystemMatrixSubstitution_homogeneousFrame
    {m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d) (c : Fin n → L) :
    ((form σ d K).map
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q))).map
        (MvPolynomial.eval₂Hom f c) =
      ∑ j, MvPolynomial.C (c j) * (q j).1.map f := by
  rw [map_form_projectiveLinearSystemMatrixSubstitution_homogeneousFrame d e q]
  simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_map]
  have hfc : (MvPolynomial.eval₂Hom f c).comp MvPolynomial.C = f := by
    ext a
    simp
  simp only [hfc]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.eval₂Hom_X']

/-- A split coefficient matrix gives a surjective substitution, and hence a
closed projective embedding of its linear system. -/
theorem projectiveLinearSystemMatrixSubstitution_surjective
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin m) K)
    (hNM : N * M = 1) :
    Function.Surjective (projectiveLinearSystemMatrixSubstitution d e M) := by
  exact (rectangularSubstitution_surjective M N hNM).comp
    (MvPolynomial.rename_surjective e.symm e.symm.surjective)

/-- The projective parameter map for a split matrix linear system. -/
noncomputable def projectiveLinearSystemMatrixToParameters
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin m) K)
    (hNM : N * M = 1) :
    projectiveLinearSystemParameters (K := K) (τ := Fin n) ⟶
      projectiveParameters K σ d :=
  projectiveLinearSystemToParameters d
    (projectiveLinearSystemMatrixSubstitution d e M)
    (fun r p hp ↦ projectiveLinearSystemMatrixSubstitution_homogeneous d e M r p hp)
    (projectiveLinearSystemMatrixSubstitution_surjective d e M N hNM)

/-- A split matrix linear system is a closed projective subspace of the
space of all degree-`d` equations. -/
instance isClosedImmersion_projectiveLinearSystemMatrixToParameters
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin m) K)
    (hNM : N * M = 1) :
    IsClosedImmersion (projectiveLinearSystemMatrixToParameters d e M N hNM) := by
  unfold projectiveLinearSystemMatrixToParameters
  infer_instance

/-- An independent frame of degree-`d` homogeneous forms presents its
projective span as a closed subsystem of the full equation space. -/
noncomputable def homogeneousFrameToParameters
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q) :
    projectiveLinearSystemParameters (K := K) (τ := Fin n) ⟶
      projectiveParameters K σ d :=
  projectiveLinearSystemMatrixToParameters d e
    (homogeneousFrameCoefficientMatrix d e q)
    (homogeneousFrameCoefficientRetractionMatrix d e q)
    (homogeneousFrameCoefficientMatrix_has_retraction d e q hqli)

/-- Every field-valued point of an independent homogeneous frame lies on a
pullback of a coefficient chart in the ambient equation parameter space. -/
theorem exists_homogeneousFrame_coefficient_chart
    {m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f)) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    ∃ i : Fin m, ∃ g : Away (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K σ d) (e i))) →+* L,
      g.comp (AllCharacteristics.GradedChart.baseMap (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (z := F (coordinate (ParameterIdeal K σ d) (e i)))) = f ∧
      Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          (F (coordinate (ParameterIdeal K σ d) (e i)))
          (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
          (by decide : 0 < 1) = t := by
  dsimp
  exact exists_projectiveLinearSystemMatrix_coefficient_chart d f e
    (homogeneousFrameCoefficientMatrix d e q)
    (homogeneousFrameCoefficientRetractionMatrix d e q)
    (homogeneousFrameCoefficientMatrix_has_retraction d e q hqli) t ht

/-- A field-valued point of a projective chart of an independent homogeneous
frame maps to the coefficient-independent classifying point of the actual
specialized frame combination. -/
theorem homogeneousFrame_chartPoint_toParameters_eq_classifying
    {m n : ℕ} {L : Type u} [Field L]
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q) (i : Fin m) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    let s := F (coordinate (ParameterIdeal K σ d) (e i))
    let hs := F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
    ∀ (g : Away (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) s →+* L)
      (f : K →+* L),
      (hbase : g.comp (AllCharacteristics.GradedChart.baseMap
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (z := s)) = f) →
      let p : MvPolynomial σ L := ∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)) *
        (q j).1.map f
      let hp : p.IsHomogeneous d := by
        apply MvPolynomial.IsHomogeneous.sum
        intro j _
        exact ((q j).2.map f).C_mul _
      let hne : p ≠ 0 := homogeneousFrame_awayMap_combination_ne_zero d e q hqli i g f hbase
      Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          s hs (by decide : 0 < 1) ≫
        homogeneousFrameToParameters d e q hqli =
      projectiveClassifyingMap p hp hne f := by
  dsimp
  intro g f hbase
  let M := homogeneousFrameCoefficientMatrix d e q
  let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    (projectiveLinearSystemMatrixSubstitution d e M) bot_le
    (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
  let s := F (coordinate (ParameterIdeal K σ d) (e i))
  let hs : s ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1 :=
    F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))
  let p := ∑ j, MvPolynomial.C (g (linearChartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) s hs j)) *
    (q j).1.map f
  let hp : p.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map f).C_mul _
  let hne : p ≠ 0 := homogeneousFrame_awayMap_combination_ne_zero d e q hqli i g f hbase
  change Spec.map (CommRingCat.ofHom g) ≫
      Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        s hs (by decide : 0 < 1) ≫
      homogeneousFrameToParameters d e q hqli =
    projectiveClassifyingMap p hp hne f
  obtain ⟨hi, hchart⟩ :=
    homogeneousFrame_awayMap_eq_projectiveEquationChartMap d e q i g f hbase
  rw [projectiveClassifyingMap_eq_chart p hp hne f (e i) hi]
  unfold projectiveEquationParameter
  rw [hchart]
  have haway :
      Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          s hs (by decide : 0 < 1) ≫
        homogeneousFrameToParameters d e q hqli =
      Spec.map (CommRingCat.ofHom
        (Away.map F (coordinate (ParameterIdeal K σ d) (e i)))) ≫
        parameterChartι K σ d (e i) := by
    unfold homogeneousFrameToParameters projectiveLinearSystemMatrixToParameters
      projectiveLinearSystemToParameters
    exact awayι_polynomialProjectiveMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q))
      (projectiveLinearSystemMatrixSubstitution_surjective d e
        (homogeneousFrameCoefficientMatrix d e q)
        (homogeneousFrameCoefficientRetractionMatrix d e q)
        (homogeneousFrameCoefficientMatrix_has_retraction d e q hqli))
      (coordinate (ParameterIdeal K σ d) (e i))
      (coordinate_mem (ParameterIdeal K σ d) (e i)) (by decide)
  change Spec.map (CommRingCat.ofHom g) ≫
      (Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        s hs (by decide : 0 < 1) ≫ homogeneousFrameToParameters d e q hqli) =
    Spec.map (CommRingCat.ofHom
      (g.comp (Away.map F (coordinate (ParameterIdeal K σ d) (e i))))) ≫
      parameterChartι K σ d (e i)
  rw [haway, ← Category.assoc, ← specMap_ringHom_comp]

/-- Any field-valued point of the projective span of an independent frame
admits a coefficient-chart normalization whose specialized equation gives its
image in the full projective parameter space. -/
theorem exists_homogeneousFrame_parameterization_eq_classifying
    {m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f)) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    ∃ i : Fin m, ∃ g : Away (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K σ d) (e i))) →+* L,
      ∃ hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (z := F (coordinate (ParameterIdeal K σ d) (e i)))) = f,
      Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          (F (coordinate (ParameterIdeal K σ d) (e i)))
          (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i)))
          (by decide : 0 < 1) = t ∧
      let p : MvPolynomial σ L := ∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
        (F (coordinate (ParameterIdeal K σ d) (e i)))
        (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))) j)) *
        (q j).1.map f
      let hp : p.IsHomogeneous d := by
        apply MvPolynomial.IsHomogeneous.sum
        intro j _
        exact ((q j).2.map f).C_mul _
      let hne : p ≠ 0 := homogeneousFrame_awayMap_combination_ne_zero
        d e q hqli i g f hbase
      t ≫ homogeneousFrameToParameters d e q hqli =
        projectiveClassifyingMap p hp hne f := by
  dsimp
  obtain ⟨i, g, hbase, hchart⟩ :=
    exists_homogeneousFrame_coefficient_chart d f e q hqli t ht
  refine ⟨i, g, hbase, hchart, ?_⟩
  rw [← hchart]
  exact homogeneousFrame_chartPoint_toParameters_eq_classifying
    d e q hqli i g f hbase

/-- A universal-family point whose parameter lies in an independent frame
comes from the hypersurface defined by the corresponding specialized frame
combination.  The lift retains both its coefficient field and ambient point. -/
theorem exists_homogeneousFrame_parameterization_universalFamily_lift
    {m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f))
    (u : Spec (.of L) ⟶ projectiveUniversalFamily K σ d)
    (hu : u ≫ projectiveUniversalToBase K σ d =
      t ≫ homogeneousFrameToParameters d e q hqli) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    ∃ i : Fin m, ∃ g : Away (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K σ d) (e i))) →+* L,
      ∃ hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (z := F (coordinate (ParameterIdeal K σ d) (e i)))) = f,
      let p : MvPolynomial σ L := ∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
        (F (coordinate (ParameterIdeal K σ d) (e i)))
        (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))) j)) *
        (q j).1.map f
      let hp : p.IsHomogeneous d := by
        apply MvPolynomial.IsHomogeneous.sum
        intro j _
        exact ((q j).2.map f).C_mul _
      ∃ x : Spec (.of L) ⟶ hypersurface p hp,
        x ≫ hypersurfaceToBase p hp = 𝟙 _ ∧
        x ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap f =
          u ≫ projectiveUniversalToAmbient K σ d := by
  dsimp
  obtain ⟨i, g, hbase, hchart, hclass⟩ :=
    exists_homogeneousFrame_parameterization_eq_classifying d f e q hqli t ht
  refine ⟨i, g, hbase, ?_⟩
  let p : MvPolynomial σ L := ∑ j, MvPolynomial.C (g (linearChartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    ((polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q)))
      (coordinate (ParameterIdeal K σ d) (e i)))
    ((polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q))).map_mem
      (coordinate_mem (ParameterIdeal K σ d) (e i))) j)) *
    (q j).1.map f
  let hp : p.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map f).C_mul _
  let hne : p ≠ 0 := homogeneousFrame_awayMap_combination_ne_zero
    d e q hqli i g f hbase
  change ∃ x : Spec (.of L) ⟶ hypersurface p hp,
    x ≫ hypersurfaceToBase p hp = 𝟙 _ ∧
    x ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap f =
      u ≫ projectiveUniversalToAmbient K σ d
  have hq : u ≫ projectiveUniversalToBase K σ d =
      projectiveClassifyingMap p hp hne f := hu.trans hclass
  refine ⟨projectiveClassifyingFiberLift p hp hne f u hq, ?_, ?_⟩
  · exact projectiveClassifyingFiberLift_comp_toBase p hp hne f u hq
  · exact projectiveClassifyingFiberLift_comp_toAmbient p hp hne f u hq

/-- A family of universal hypersurface points over one field-valued frame
parameter has a simultaneous lift to one specialized frame equation.  The
coefficient chart, equation, and scalar extension are shared by every member
of the family. -/
theorem exists_homogeneousFrame_parameterization_universalFamily_lifts
    {m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f))
    {ι : Type} (u : ι → (Spec (.of L) ⟶ projectiveUniversalFamily K σ d))
    (hu : ∀ a, u a ≫ projectiveUniversalToBase K σ d =
      t ≫ homogeneousFrameToParameters d e q hqli) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    ∃ i : Fin m, ∃ g : Away (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K σ d) (e i))) →+* L,
      ∃ hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (z := F (coordinate (ParameterIdeal K σ d) (e i)))) = f,
      let p : MvPolynomial σ L := ∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
        (F (coordinate (ParameterIdeal K σ d) (e i)))
        (F.map_mem (coordinate_mem (ParameterIdeal K σ d) (e i))) j)) *
        (q j).1.map f
      let hp : p.IsHomogeneous d := by
        apply MvPolynomial.IsHomogeneous.sum
        intro j _
        exact ((q j).2.map f).C_mul _
      ∃ x : ι → (Spec (.of L) ⟶ hypersurface p hp),
        (∀ a, x a ≫ hypersurfaceToBase p hp = 𝟙 _) ∧
        ∀ a, x a ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap f =
          u a ≫ projectiveUniversalToAmbient K σ d := by
  dsimp
  obtain ⟨i, g, hbase, hchart, hclass⟩ :=
    exists_homogeneousFrame_parameterization_eq_classifying d f e q hqli t ht
  refine ⟨i, g, hbase, ?_⟩
  let p : MvPolynomial σ L := ∑ j, MvPolynomial.C (g (linearChartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    ((polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q)))
      (coordinate (ParameterIdeal K σ d) (e i)))
    ((polynomialQuotientGradingMap (ParameterIdeal K σ d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q))).map_mem
      (coordinate_mem (ParameterIdeal K σ d) (e i))) j)) *
    (q j).1.map f
  let hp : p.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map f).C_mul _
  let hne : p ≠ 0 := homogeneousFrame_awayMap_combination_ne_zero
    d e q hqli i g f hbase
  change ∃ x : ι → (Spec (.of L) ⟶ hypersurface p hp),
    (∀ a, x a ≫ hypersurfaceToBase p hp = 𝟙 _) ∧
    ∀ a, x a ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap f =
      u a ≫ projectiveUniversalToAmbient K σ d
  have hq : ∀ a, u a ≫ projectiveUniversalToBase K σ d =
      projectiveClassifyingMap p hp hne f := fun a ↦ (hu a).trans hclass
  refine ⟨fun a ↦ projectiveClassifyingFiberLift p hp hne f (u a) (hq a), ?_, ?_⟩
  · intro a
    exact projectiveClassifyingFiberLift_comp_toBase p hp hne f (u a) (hq a)
  · intro a
    exact projectiveClassifyingFiberLift_comp_toAmbient p hp hne f (u a) (hq a)

/-- Pair an ambient family with a family of equations in the projective span
of an independent homogeneous frame. -/
noncomputable def homogeneousFrameIncidenceParameterMap
    {m n : ℕ} {B : Scheme.{u}}
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K))
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (s : B ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n)) :
    B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K) ⨯ projectiveParameters K σ d :=
  Limits.prod.lift a (s ≫ homogeneousFrameToParameters d e q hqli)

/-- For a family of equations in the projective span of an independent
homogeneous frame, the locus on which the equation vanishes at the ambient
point is closed.  This is the actual bad locus whose properness is used in a
generic-section argument. -/
theorem isClosed_homogeneousFrameIncidence_badLocus
    {m n : ℕ} {B : Scheme.{u}}
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K))
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (s : B ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n)) :
    IsClosed (homogeneousFrameIncidenceParameterMap d a e q hqli s ⁻¹'
      Set.range (projectiveUniversalIncidence K σ d)) := by
  exact (isClosed_range_projectiveUniversalIncidence K σ d).preimage
    (homogeneousFrameIncidenceParameterMap d a e q hqli s).continuous

/-- A single parameter value at which the selected equation does not vanish
at its ambient point proves that the frame-incidence bad locus is proper. -/
theorem homogeneousFrameIncidence_badLocus_ne_univ_of_exists
    {m n : ℕ} {B : Scheme.{u}}
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K))
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (s : B ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (hgood : ∃ b : B,
      b ∉ homogeneousFrameIncidenceParameterMap d a e q hqli s ⁻¹'
        Set.range (projectiveUniversalIncidence K σ d)) :
    homogeneousFrameIncidenceParameterMap d a e q hqli s ⁻¹'
      Set.range (projectiveUniversalIncidence K σ d) ≠ Set.univ := by
  rintro hbad
  obtain ⟨b, hb⟩ := hgood
  exact hb (by rw [hbad]; exact Set.mem_univ b)

/-- The projective span of an independent homogeneous frame is closed. -/
instance isClosedImmersion_homogeneousFrameToParameters
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q) :
    IsClosedImmersion (homogeneousFrameToParameters d e q hqli) := by
  unfold homogeneousFrameToParameters
  infer_instance

end PfaffianDescent
