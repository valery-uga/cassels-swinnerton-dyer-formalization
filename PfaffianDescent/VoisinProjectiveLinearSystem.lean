import PfaffianDescent.VoisinSectionChoice
import PfaffianDescent.ProjectiveLinearSystem
import PfaffianDescent.CubicSurfacePointEvaluation
import AllCharacteristics.UniversalProjectiveFiniteIncidence
import AllCharacteristics.OrderedConfigurationProjectiveIncidence
import AllCharacteristics.ProjectiveConfigurationGenericImageAvoidance
import AllCharacteristics.VoisinGenericCubicConfiguration

/-!
# Projective systems from Voisin's chosen cubic sections

The cubic frame selected from the restriction kernel is an actual projective
linear subsystem of the projective space of all cubics.  This file makes that
bridge explicit, so the universal projective incidence results apply to the
sections selected in the Voisin argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.UniversalHomogeneous
open AllCharacteristics.HomogeneousProjective

universe u

section LinearAlgebra

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- Coercing a linearly independent family in a submodule to its ambient
module preserves linear independence. -/
theorem linearIndependent_submodule_coe
    (W : Submodule K V) {n : ℕ} (v : Fin n → W)
    (h : LinearIndependent K v) :
    LinearIndependent K (fun i => (v i : V)) :=
  h.map' W.subtype (LinearMap.ker_eq_bot.mpr W.subtype_injective)

end LinearAlgebra

section Cubics

variable {K A : Type u} [Field K] [Infinite K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]

/-- Voisin's selected cubic frame, regarded directly as a linearly independent
family in the degree-three homogeneous part. -/
theorem choose_cubic_vanishing_homogeneous_frame
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx) :
    ∃ v : Fin 4 → homogeneousSubmodule (Fin 4) K 3,
      (v 0).1 = p ∧ LinearIndependent K v ∧
        ∀ i, (v i).1.eval₂ (algebraMap K A) x = 0 := by
  obtain ⟨v, hv0, hli, hv⟩ :=
    choose_cubic_vanishing_frame_data p hp hne x hpx hsections
  let w : Fin 4 → homogeneousSubmodule (Fin 4) K 3 := fun i => (v i).1
  have hwli : LinearIndependent K w := by
    exact linearIndependent_submodule_coe
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)) v hli
  refine ⟨w, ?_, hwli, ?_⟩
  · simpa only [w] using hv0
  · intro i
    exact (hv i).2

/-- The selected cubic frame supplies a closed projective linear subsystem of
the full projective space of cubic equations. -/
theorem choose_cubic_vanishing_frame_projective_system
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx) :
    ∃ (m : ℕ) (e : Fin m ≃ Monomials (Fin 4) 3)
      (v : Fin 4 → homogeneousSubmodule (Fin 4) K 3)
      (hqli : LinearIndependent K v),
      (v 0).1 = p ∧
        (∀ i, (v i).1.eval₂ (algebraMap K A) x = 0) ∧
        IsClosedImmersion (homogeneousFrameToParameters 3 e v hqli) := by
  classical
  let m := Fintype.card (Monomials (Fin 4) 3)
  let e : Fin m ≃ Monomials (Fin 4) 3 := (Fintype.equivFin _).symm
  obtain ⟨v, hv0, hvli, hv⟩ :=
    choose_cubic_vanishing_homogeneous_frame p hp hne x hpx hsections
  refine ⟨m, e, v, hvli, hv0, hv, ?_⟩
  infer_instance

end Cubics

section FieldExtensionFrameEvaluation

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A square interpolation set for a homogeneous frame remains detecting
after every field extension.  Coefficients of a linear combination of the
frame that vanishes on all selected cone points must therefore be zero over
the extension field as well. -/
theorem homogeneousFrame_fieldExtension_coefficients_zero_of_evaluation_bijective
    {L : Type u} [Field L] (f : K →+* L)
    (p : MvPolynomial (Fin 4) K) {d n : ℕ}
    (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (s : Finset (cubicSurfaceAffinePoints p)) (hscard : s.card = n)
    (hbij : Function.Bijective ((finsetEvaluation s).comp
      ((cubicSurfacePointEvaluation p
        (homogeneousSubmodule (Fin 4) K d)).comp (homogeneousFrameMap d q))))
    (c : Fin n → L)
    (hvan : ∀ x ∈ s,
      MvPolynomial.aeval (fun i => f (x.1 i))
        (∑ j, MvPolynomial.C (c j) * (q j).1.map f) = 0) :
    c = 0 := by
  classical
  let e : Fin n ≃ s := Fintype.equivOfCardEq (by simpa using hscard.symm)
  let A : Matrix (Fin n) (Fin n) K :=
    fun i j => MvPolynomial.aeval (e i).1.1 (q j).1
  have hA_eval (b : Fin n → K) (i : Fin n) :
      A.mulVec b i = MvPolynomial.aeval (e i).1.1
        ((homogeneousFrameMap d q b).1) := by
    rw [homogeneousFrameMap, Fintype.linearCombination_apply]
    simp only [A, Matrix.mulVec, Submodule.coe_sum, Submodule.coe_smul,
      MvPolynomial.aeval_sum, smul_eq_C_mul, map_mul,
      MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hAinj : Function.Injective A.mulVec := by
    intro b b' hbb'
    apply hbij.1
    ext x
    obtain ⟨i, rfl⟩ := e.surjective x
    change MvPolynomial.aeval (e i).1.1 ((homogeneousFrameMap d q b).1) =
      MvPolynomial.aeval (e i).1.1 ((homogeneousFrameMap d q b').1)
    rw [← hA_eval b i, ← hA_eval b' i]
    exact congrFun hbb' i
  have hAmapinj : Function.Injective (A.map f).mulVec :=
    Matrix.map_mulVec_injective_of_mulVec_injective f A hAinj
  have hAmap_eval (b : Fin n → L) (i : Fin n) :
      (A.map f).mulVec b i =
        MvPolynomial.aeval (fun k => f ((e i).1.1 k))
          (∑ j, MvPolynomial.C (b j) * (q j).1.map f) := by
    change (∑ j, f (MvPolynomial.aeval (e i).1.1 (q j).1) * b j) = _
    rw [MvPolynomial.aeval_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply]
    have hmap :
        MvPolynomial.aeval (fun k => f ((e i).1.1 k)) ((q j).1.map f) =
          f (MvPolynomial.aeval (e i).1.1 (q j).1) :=
      aeval_map_of_fieldHom f (q j).1 (e i).1.1
    rw [hmap]
    exact mul_comm _ _
  have hcoeff : (A.map f).mulVec c = 0 := by
    funext i
    rw [hAmap_eval c i]
    exact hvan (e i).1 (e i).2
  exact hAmapinj (by simpa using hcoeff)

/-- If a homogeneous frame is represented by vectors in a polynomial
submodule, its polynomial-valued linear combinations agree with the intrinsic
homogeneous-frame combinations. -/
theorem homogeneousFrameMap_coe_eq_submodule_linearCombination
    {d n : ℕ} (W : Submodule K (MvPolynomial (Fin 4) K))
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1)
    (b : Fin n → K) :
    (Fintype.linearCombination K qW b : MvPolynomial (Fin 4) K) =
      (homogeneousFrameMap d q b).1 := by
  rw [homogeneousFrameMap, Fintype.linearCombination_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change ∑ i, b i • (qW i : MvPolynomial (Fin 4) K) =
    (∑ i, b i • q i : homogeneousSubmodule (Fin 4) K d).1
  rw [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hq i]
  rfl

/-- A square interpolation set for a polynomial submodule remains detecting
after scalar extension for any linearly independent homogeneous frame it
contains. -/
theorem homogeneousFrame_fieldExtension_coefficients_zero_of_submodule_evaluation_injective
    {L : Type u} [Field L] (f : K →+* L)
    (p : MvPolynomial (Fin 4) K) {d n : ℕ}
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1)
    (hqli : LinearIndependent K qW)
    (s : Finset (cubicSurfaceAffinePoints p)) (hscard : s.card = n)
    (hinj : Function.Injective ((finsetEvaluation s).comp
      (cubicSurfacePointEvaluation p W)))
    (c : Fin n → L)
    (hvan : ∀ x ∈ s,
      MvPolynomial.aeval (fun i => f (x.1 i))
        (∑ j, MvPolynomial.C (c j) * (q j).1.map f) = 0) :
    c = 0 := by
  classical
  let e : Fin n ≃ s := Fintype.equivOfCardEq (by simpa using hscard.symm)
  let A : Matrix (Fin n) (Fin n) K :=
    fun i j => MvPolynomial.aeval (e i).1.1 (q j).1
  have hA_eval (b : Fin n → K) (i : Fin n) :
      A.mulVec b i = MvPolynomial.aeval (e i).1.1
        ((homogeneousFrameMap d q b).1) := by
    rw [homogeneousFrameMap, Fintype.linearCombination_apply]
    simp only [A, Matrix.mulVec, Submodule.coe_sum, Submodule.coe_smul,
      MvPolynomial.aeval_sum, smul_eq_C_mul, map_mul,
      MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hAinj : Function.Injective A.mulVec := by
    intro b b' hbb'
    apply hqli.fintypeLinearCombination_injective
    apply hinj
    ext x
    obtain ⟨i, rfl⟩ := e.surjective x
    change MvPolynomial.aeval (e i).1.1
        ((Fintype.linearCombination K qW b : W) : MvPolynomial (Fin 4) K) =
      MvPolynomial.aeval (e i).1.1
        ((Fintype.linearCombination K qW b' : W) : MvPolynomial (Fin 4) K)
    rw [homogeneousFrameMap_coe_eq_submodule_linearCombination W qW q hq b,
      homogeneousFrameMap_coe_eq_submodule_linearCombination W qW q hq b',
      ← hA_eval b i, ← hA_eval b' i]
    exact congrFun hbb' i
  have hAmapinj : Function.Injective (A.map f).mulVec :=
    Matrix.map_mulVec_injective_of_mulVec_injective f A hAinj
  have hAmap_eval (b : Fin n → L) (i : Fin n) :
      (A.map f).mulVec b i =
        MvPolynomial.aeval (fun k => f ((e i).1.1 k))
          (∑ j, MvPolynomial.C (b j) * (q j).1.map f) := by
    change (∑ j, f (MvPolynomial.aeval (e i).1.1 (q j).1) * b j) = _
    rw [MvPolynomial.aeval_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply]
    have hmap :
        MvPolynomial.aeval (fun k => f ((e i).1.1 k)) ((q j).1.map f) =
          f (MvPolynomial.aeval (e i).1.1 (q j).1) :=
      aeval_map_of_fieldHom f (q j).1 (e i).1.1
    rw [hmap]
    exact mul_comm _ _
  have hcoeff : (A.map f).mulVec c = 0 := by
    funext i
    rw [hAmap_eval c i]
    exact hvan (e i).1 (e i).2
  exact hAmapinj (by simpa using hcoeff)

/-- A larger detecting set for a finite-dimensional polynomial submodule
detects every scalar extension of any independent homogeneous frame forming a
basis of that submodule.  A square interpolation subset is extracted only for
the matrix argument; vanishing may be assumed on the original larger set. -/
theorem homogeneousFrame_fieldExtension_coefficients_zero_of_large_submodule_evaluation_injective
    {L : Type u} [Field L] (f : K →+* L)
    (p : MvPolynomial (Fin 4) K) {d n : ℕ}
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1)
    (hqli : LinearIndependent K qW)
    (hn : Module.finrank K W = n)
    (u : Finset (cubicSurfaceAffinePoints p))
    (hinj : Function.Injective ((finsetEvaluation u).comp
      (cubicSurfacePointEvaluation p W)))
    (c : Fin n → L)
    (hvan : ∀ x ∈ u,
      MvPolynomial.aeval (fun i => f (x.1 i))
        (∑ j, MvPolynomial.C (c j) * (q j).1.map f) = 0) :
    c = 0 := by
  obtain ⟨s, hsu, hscard, hbij⟩ :=
    exists_finset_subset_evaluation_bijective
      (cubicSurfacePointEvaluation p W) u hinj
  apply homogeneousFrame_fieldExtension_coefficients_zero_of_submodule_evaluation_injective
    f p W qW q hq hqli s (hscard.trans hn) hbij.1 c
  intro x hx
  exact hvan x (hsu hx)

/-- The preceding extension-stable interpolation statement is equivalently
injectivity of restriction of the scalar-extended homogeneous frame to the
chosen finite set of cubic-surface cone points.  This is the direct
restriction-map form used in Voisin's moving-divisor argument: two sections
of the system which agree at every marked point already have equal
coefficients. -/
theorem homogeneousFrame_fieldExtension_evaluation_injective_of_large_submodule_evaluation_injective
    {L : Type u} [Field L] (f : K →+* L)
    (p : MvPolynomial (Fin 4) K) {d n : ℕ}
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1)
    (hqli : LinearIndependent K qW)
    (hn : Module.finrank K W = n)
    (u : Finset (cubicSurfaceAffinePoints p))
    (hinj : Function.Injective ((finsetEvaluation u).comp
      (cubicSurfacePointEvaluation p W))) :
    Function.Injective (fun c : Fin n → L => fun x : {x // x ∈ u} =>
      MvPolynomial.aeval (fun i => f (x.1.1 i))
        (∑ j, MvPolynomial.C (c j) * (q j).1.map f)) := by
  intro c b hcb
  have hvan : ∀ x ∈ u, MvPolynomial.aeval (fun i => f (x.1 i))
      (∑ j, MvPolynomial.C ((c - b) j) * (q j).1.map f) = 0 := by
    intro x hx
    have hcomb :
        (∑ j, MvPolynomial.C ((c - b) j) * (q j).1.map f) =
        (∑ j, MvPolynomial.C (c j) * (q j).1.map f) -
          (∑ j, MvPolynomial.C (b j) * (q j).1.map f) := by
      simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    have heq :
        MvPolynomial.aeval (fun i => f (x.1 i))
          (∑ j, MvPolynomial.C (c j) * (q j).1.map f) =
        MvPolynomial.aeval (fun i => f (x.1 i))
          (∑ j, MvPolynomial.C (b j) * (q j).1.map f) := by
      simpa using congrFun hcb ⟨x, hx⟩
    rw [hcomb, map_sub, heq, sub_self]
  have hzero : c - b = 0 :=
    homogeneousFrame_fieldExtension_coefficients_zero_of_large_submodule_evaluation_injective
      f p W qW q hq hqli hn u hinj (c - b) hvan
  exact sub_eq_zero.mp hzero

end FieldExtensionFrameEvaluation

section CubicSurfaceFrameRoots

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A simultaneous universal-incidence family over one frame parameter gives
one specialized frame equation vanishing on each chosen cubic-surface cone
point.  The marked points may be indexed by an arbitrary type; all lifts use
the same coefficient chart and the same equation. -/
theorem exists_homogeneousFrame_parameterization_roots_of_cubicSurfaceAffinePoints
    {d m n : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (e : Fin m ≃ Monomials (Fin 4) d)
    (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hqli : LinearIndependent K q)
    (t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f))
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (c : Fin 4 → K) {ι : Type} (v : ι → cubicSurfaceAffinePoints cubic)
    (hcommon : ∀ a,
      MvPolynomial.aeval (v a).1 (homogeneousLinearForm c) ≠ 0)
    (u : ι → (Spec (.of L) ⟶ projectiveUniversalFamily K (Fin 4) d))
    (hu : ∀ a, u a ≫ projectiveUniversalToBase K (Fin 4) d =
      t ≫ homogeneousFrameToParameters d e q hqli)
    (hambient : ∀ a, u a ≫ projectiveUniversalToAmbient K (Fin 4) d =
      Spec.map (CommRingCat.ofHom f) ≫
        (cubicSurfaceAffinePointLinearNormalizedProjectivePoint cubic hcubic c (v a)
          (hcommon a) ≫ hypersurfaceToAmbient cubic hcubic)) :
    let M := homogeneousFrameCoefficientMatrix d e q
    let F := polynomialQuotientGradingMap (ParameterIdeal K (Fin 4) d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e M) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e M)
    ∃ i : Fin m, ∃ g : HomogeneousLocalization.Away (grading
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (F (coordinate (ParameterIdeal K (Fin 4) d) (e i))) →+* L,
      let p : MvPolynomial (Fin 4) L := ∑ j, MvPolynomial.C (g (linearChartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
        (F (coordinate (ParameterIdeal K (Fin 4) d) (e i)))
        (F.map_mem (coordinate_mem (ParameterIdeal K (Fin 4) d) (e i))) j)) *
        (q j).1.map f
      p ≠ 0 ∧ ∀ a, MvPolynomial.aeval (fun k ↦ f ((v a).1 k)) p = 0 := by
  dsimp
  obtain ⟨i, g, hbase, x, hxbase, hxambient⟩ :=
    exists_homogeneousFrame_parameterization_universalFamily_lifts
      d f e q hqli t ht u hu
  refine ⟨i, g, ?_⟩
  let p : MvPolynomial (Fin 4) L := ∑ j, MvPolynomial.C (g (linearChartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    ((polynomialQuotientGradingMap (ParameterIdeal K (Fin 4) d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q)))
      (coordinate (ParameterIdeal K (Fin 4) d) (e i)))
    ((polynomialQuotientGradingMap (ParameterIdeal K (Fin 4) d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q))).map_mem
      (coordinate_mem (ParameterIdeal K (Fin 4) d) (e i))) j)) *
    (q j).1.map f
  let hp : p.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact ((q j).2.map f).C_mul _
  let hne : p ≠ 0 := homogeneousFrame_awayMap_combination_ne_zero
    d e q hqli i g f hbase
  change p ≠ 0 ∧ ∀ a, MvPolynomial.aeval (fun k ↦ f ((v a).1 k)) p = 0
  refine ⟨hne, ?_⟩
  intro a
  obtain ⟨j, w, h, hw, hcoordinates, hambientChart⟩ :=
    exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint_fieldExtension
      f cubic hcubic c (v a) (hcommon a)
  have hrootBase : x a ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    have hid : CommRingCat.ofHom (RingHom.id L) = 𝟙 _ := rfl
    rw [hid, Spec.map_id]
    exact hxbase a
  have hrootAmbient : x a ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap f =
      Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
          (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)
          (by decide : 0 < 1) := by
    calc
      x a ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap f =
          u a ≫ projectiveUniversalToAmbient K (Fin 4) d := hxambient a
      _ = Spec.map (CommRingCat.ofHom f) ≫
          (cubicSurfaceAffinePointLinearNormalizedProjectivePoint cubic hcubic c (v a)
            (hcommon a) ≫ hypersurfaceToAmbient cubic hcubic) := hambient a
      _ = Spec.map (CommRingCat.ofHom h) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)
            (by decide : 0 < 1) := hambientChart.symm
  have hzero : MvPolynomial.aeval
      (fun l ↦ h (AllCharacteristics.GradedChart.normalized
        (MvPolynomial.homogeneousSubmodule (Fin 4) K)
        (MvPolynomial.isHomogeneous_X K j) (MvPolynomial.X l)
        (MvPolynomial.isHomogeneous_X K l))) p = 0 := by
    simpa only [MvPolynomial.map_id] using
      (AllCharacteristics.HomogeneousProjective.aeval_map_eq_zero_of_ambient_eq
        f p hp (RingHom.id L) (x a) hrootBase j h hrootAmbient)
  have hzero' : MvPolynomial.aeval
      (fun l ↦ f ((↑(w⁻¹) : K) *
        cubicSurfaceAffinePointNormalizedConeCoordinates c (v a).1 l)) p = 0 := by
    have hcoordinates' :
        (fun l ↦ f ((↑(w⁻¹) : K) *
          cubicSurfaceAffinePointNormalizedConeCoordinates c (v a).1 l)) =
        fun l ↦ h (AllCharacteristics.GradedChart.normalized
          (MvPolynomial.homogeneousSubmodule (Fin 4) K)
          (MvPolynomial.isHomogeneous_X K j) (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l)) := by
      funext l
      exact (hcoordinates l).symm
    rw [hcoordinates']
    exact hzero
  have hscale :
      (fun l ↦ f ((↑(w⁻¹) : K) *
        cubicSurfaceAffinePointNormalizedConeCoordinates c (v a).1 l)) =
      f ((↑(w⁻¹) : K) *
        (MvPolynomial.aeval (v a).1 (homogeneousLinearForm c))⁻¹) •
        (fun l ↦ f ((v a).1 l)) := by
    ext l
    rw [cubicSurfaceAffinePointNormalizedConeCoordinates]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.map_mul]
    ring
  have hscalarK : (↑(w⁻¹) : K) *
      (MvPolynomial.aeval (v a).1 (homogeneousLinearForm c))⁻¹ ≠ 0 :=
    mul_ne_zero (Units.ne_zero (w⁻¹)) (inv_ne_zero (hcommon a))
  have hscalar : f ((↑(w⁻¹) : K) *
      (MvPolynomial.aeval (v a).1 (homogeneousLinearForm c))⁻¹) ≠ 0 := by
    intro hzeroScalar
    apply hscalarK
    apply f.injective
    simpa using hzeroScalar
  apply aeval_eq_zero_of_smul_eq_zero_of_isHomogeneous p hp
    (f ((↑(w⁻¹) : K) *
      (MvPolynomial.aeval (v a).1 (homogeneousLinearForm c))⁻¹)) hscalar
    (fun l ↦ f ((v a).1 l))
  rw [← hscale]
  exact hzero'

/-- The eleven-point evaluation witness excludes a simultaneous
universal-incidence family for an independent frame spanning the detected
homogeneous submodule.  This is the algebraic contradiction used after a bad
finite-incidence point has been lifted to one coefficient field. -/
theorem homogeneousFrame_parameterization_universalFamily_points_impossible_of_submodule_evaluation_injective
    {d m n r : ℕ} {L : Type u} [Field L] (f : K →+* L)
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (S : Finset (cubicSurfaceAffinePoints cubic))
    (hinj : Function.Injective ((finsetEvaluation S).comp
      (cubicSurfacePointEvaluation cubic W)))
    (c : Fin 4 → K)
    (hcommon : ∀ y ∈ S,
      MvPolynomial.aeval y.1 (homogeneousLinearForm c) ≠ 0)
    (E : Fin r ≃ S)
    (e : Fin m ≃ Monomials (Fin 4) d)
    (t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f))
    (u : Fin r → (Spec (.of L) ⟶ projectiveUniversalFamily K (Fin 4) d))
    (hu : ∀ a, u a ≫ projectiveUniversalToBase K (Fin 4) d =
      t ≫ homogeneousFrameToParameters d e q hqliq)
    (hambient : ∀ a, u a ≫ projectiveUniversalToAmbient K (Fin 4) d =
      Spec.map (CommRingCat.ofHom f) ≫
        (cubicSurfaceAffinePointLinearNormalizedProjectivePoint cubic hcubic c (E a).1
          (hcommon (E a).1 (E a).2) ≫ hypersurfaceToAmbient cubic hcubic)) :
    False := by
  obtain ⟨i, g, hne, hroot⟩ :=
    exists_homogeneousFrame_parameterization_roots_of_cubicSurfaceAffinePoints
      f e q hqliq t ht cubic hcubic c (fun a ↦ (E a).1)
      (fun a ↦ hcommon (E a).1 (E a).2) u hu hambient
  apply hne
  let coefficients : Fin n → L := fun j ↦ g (linearChartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    ((polynomialQuotientGradingMap (ParameterIdeal K (Fin 4) d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q)))
      (coordinate (ParameterIdeal K (Fin 4) d) (e i)))
    ((polynomialQuotientGradingMap (ParameterIdeal K (Fin 4) d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e q)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e q))).map_mem
      (coordinate_mem (ParameterIdeal K (Fin 4) d) (e i))) j)
  have hcoefficients : coefficients = 0 :=
    homogeneousFrame_fieldExtension_coefficients_zero_of_large_submodule_evaluation_injective
      f cubic W qW q hq hqli hn S hinj coefficients (by
        intro y hy
        obtain ⟨a, ha⟩ := E.surjective ⟨y, hy⟩
        have hpoint : (E a).1 = y := congrArg Subtype.val ha
        simpa only [coefficients, hpoint] using hroot a)
  change ∑ j, MvPolynomial.C (coefficients j) * (q j).1.map f = 0
  rw [hcoefficients]
  simp

/-- A field-valued ordered configuration whose marked cone points detect an
independent homogeneous system lies outside that system's finite universal
incidence locus.  The number of marked points is arbitrary. -/
theorem exists_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_configuration
    {d m n k : ℕ}
    [NeZero k]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    (S : Finset (cubicSurfaceAffinePoints cubic))
    (hinj : Function.Injective ((finsetEvaluation S).comp
      (cubicSurfacePointEvaluation cubic W)))
    (c : Fin 4 → K)
    (hcommon : ∀ y ∈ S,
      MvPolynomial.aeval y.1 (homogeneousLinearForm c) ≠ 0)
    (E : Fin k ≃ S)
    (points : Fin k → (Spec (.of K) ⟶
      hypersurface cubic hcubic))
    (a : Spec (.of K) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).left)
    (hpoints : ∀ i, points i =
      cubicSurfaceAffinePointLinearNormalizedProjectivePoint cubic hcubic c (E i).1
        (hcommon (E i).1 (E i).2))
    (haCoordinates : ∀ i, (a ≫ Over.Hom.left
      (orderedFamilyConfigurationι (hypersurfaceToBase cubic hcubic) k)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left = points i)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)] :
    ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep k
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq) := by
  let C := (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).left
  let marked := @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
    (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep k
    (hypersurfaceToAmbient cubic hcubic)
  let x : C := a (IsLocalRing.closedPoint K)
  refine ⟨x, ?_⟩
  intro hx
  obtain ⟨z, hzfst, hzinc⟩ :=
    exists_parameter_of_mem_projectiveUniversalFiniteIncidenceBadLocus
      K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) marked
      (homogeneousFrameToParameters d e q hqliq) hx
  obtain ⟨L, hL, r, u, hrange, hu⟩ :=
    exists_common_fieldPoint_of_mem_all_parameterMap_range
      K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) marked
      (homogeneousFrameToParameters d e q hqliq) z hzinc
  letI : Field L := hL
  let cL : Spec (.of L) := IsLocalRing.closedPoint L
  have hrcL : r cL = z := by
    have hmem : r cL ∈ Set.range r := ⟨cL, rfl⟩
    rw [hrange] at hmem
    simpa only [Set.mem_singleton_iff] using hmem
  have hmarked : ∀ i, a ≫ marked i =
      points i ≫ hypersurfaceToAmbient cubic hcubic := by
    intro i
    unfold marked orderedConfigurationProjectivePoint
    change a ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase cubic hcubic) k) ≫
        Over.Hom.left (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i) ≫
        hypersurfaceToAmbient cubic hcubic = _
    simpa only [← Category.assoc] using
      congrArg (fun g ↦ g ≫ hypersurfaceToAmbient cubic hcubic) (haCoordinates i)
  have hfactor : ∀ i : Fin k, ∃ b : Spec (.of L) ⟶ Spec (.of K),
      b ≫ points i ≫ hypersurfaceToAmbient cubic hcubic =
        r ≫ pullback.fst (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫ marked i := by
    intro i
    rw [hpoints i]
    apply exists_spec_factor_cubicSurfaceAffinePointLinearNormalizedProjectivePoint_of_mem_ambient_range
      cubic hcubic c (E i).1 (hcommon (E i).1 (E i).2)
    refine ⟨IsLocalRing.closedPoint K, ?_⟩
    have hpoint :
        (r ≫ pullback.fst (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫ marked i) cL =
          (points i ≫ hypersurfaceToAmbient cubic hcubic) (IsLocalRing.closedPoint K) := by
      change marked i (pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (r cL)) = _
      rw [hrcL, hzfst]
      calc
        marked i (a (IsLocalRing.closedPoint K)) =
            (a ≫ marked i) (IsLocalRing.closedPoint K) :=
              (Scheme.Hom.comp_apply _ _ _).symm
        _ = (points i ≫ hypersurfaceToAmbient cubic hcubic)
            (IsLocalRing.closedPoint K) := by rw [hmarked i]
    simpa only [hpoints i] using hpoint.symm
  choose b hb using hfactor
  have hbsurface : ∀ i,
      b i ≫ points i =
        ((r ≫ pullback.fst (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left := by
    intro i
    apply (cancel_mono (hypersurfaceToAmbient cubic hcubic)).mp
    calc
      (b i ≫ points i) ≫ hypersurfaceToAmbient cubic hcubic = b i ≫ points i ≫
          hypersurfaceToAmbient cubic hcubic := Category.assoc _ _ _
      _ = r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
            (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫
            marked i := hb i
      _ = r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
            (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι ≫
            (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left ≫
            hypersurfaceToAmbient cubic hcubic := by rfl
      _ = ((r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
            (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left ≫
            hypersurfaceToAmbient cubic hcubic := (Category.assoc _ _ _).symm
  have hcoordinateBase : ∀ i,
      (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left ≫
          hypersurfaceToBase cubic hcubic =
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom := by
    intro i
    change Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase cubic hcubic) k) ≫
      ((orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left ≫
        hypersurfaceToBase cubic hcubic) = _
    rw [orderedFamilyCoordinate_toBase]
    exact (orderedFamilyConfigurationι (hypersurfaceToBase cubic hcubic) k).w
  have hcoordinateBaseLeft : ∀ i,
      ((orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left) ≫
          hypersurfaceToBase cubic hcubic =
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom := by
    intro i
    change (Over.Hom.left (orderedFamilyConfigurationι
      (hypersurfaceToBase cubic hcubic) k) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left) ≫
      hypersurfaceToBase cubic hcubic = _
    rw [Category.assoc]
    exact hcoordinateBase i
  have hbsurfaceBase : ∀ i,
      (b i ≫ points i) ≫ hypersurfaceToBase cubic hcubic =
        (((r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left) ≫
          hypersurfaceToBase cubic hcubic := by
    intro i
    exact congrArg (fun g ↦ g ≫ hypersurfaceToBase cubic hcubic) (hbsurface i)
  have hbbase : ∀ i,
      b i ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) =
        r ≫ pullback.fst (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom := by
    intro i
    calc
      b i ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) =
          (b i ≫ points i) ≫ hypersurfaceToBase cubic hcubic := by
            rw [Category.assoc, hpoints i,
              cubicSurfaceAffinePointLinearNormalizedProjectivePoint_toBase]
      _ = (((r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left) ≫
          hypersurfaceToBase cubic hcubic := hbsurfaceBase i
      _ = r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom := by
            calc
              (((r ≫ pullback.fst
                  (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                  (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
                  (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι) ≫
                  (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left) ≫
                  hypersurfaceToBase cubic hcubic =
                  (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
                    ((orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι ≫
                      ((orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left ≫
                        hypersurfaceToBase cubic hcubic)) := by
                          calc
                            (((r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                                (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
                                (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι) ≫
                                (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left) ≫
                                hypersurfaceToBase cubic hcubic =
                              ((r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                                (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
                                (orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι) ≫
                                ((orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left ≫
                                  hypersurfaceToBase cubic hcubic) := Category.assoc _ _ _
                            _ = (r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                                (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
                                ((orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι ≫
                                  ((orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left ≫
                                    hypersurfaceToBase cubic hcubic)) := Category.assoc _ _ _
              _ = (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫
                    (((orderedFamilyConfigurationOpen (hypersurfaceToBase cubic hcubic) k).ι ≫
                      (orderedFamilyCoordinate (hypersurfaceToBase cubic hcubic) k i).left) ≫
                      hypersurfaceToBase cubic hcubic) := by
                        exact congrArg (fun g ↦
                          (r ≫ pullback.fst
                            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                            (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫ g)
                          (Category.assoc _ _ _).symm
              _ = _ := by
                exact congrArg (fun g ↦
                  (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))) ≫ g)
                  (hcoordinateBaseLeft i)
  have hbeq : ∀ i, b i = b 0 := by
    intro i
    have hbbase' : ∀ i, b i = r ≫ pullback.fst
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom := by
      intro i
      simpa only [show CommRingCat.ofHom (RingHom.id K) = 𝟙 _ by rfl,
        Spec.map_id, Category.comp_id] using hbbase i
    exact (hbbase' i).trans (hbbase' 0).symm
  let f : K →+* L := (Spec.preimage (b 0)).hom
  have hf : Spec.map (CommRingCat.ofHom f) = b 0 := Spec.map_preimage _
  let t : Spec (.of L) ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n) :=
    r ≫ pullback.snd
      (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
  have ht : t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
      Spec.map (CommRingCat.ofHom f) := by
    calc
      t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
          r ≫ pullback.fst (orderedFamilyConfigurationOver
            (hypersurfaceToBase cubic hcubic) k).hom
            (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom := by
              dsimp [t]
              rw [Category.assoc, pullback.condition]
      _ = b 0 := by
        have h := hbbase 0
        simpa only [show CommRingCat.ofHom (RingHom.id K) = 𝟙 _ by rfl,
          Spec.map_id, Category.comp_id] using h.symm
      _ = Spec.map (CommRingCat.ofHom f) := hf.symm
  have huBase : ∀ i, u i ≫ projectiveUniversalToBase K (Fin 4) d =
      t ≫ homogeneousFrameToParameters d e q hqliq := by
    intro i
    calc
      u i ≫ projectiveUniversalToBase K (Fin 4) d =
          u i ≫ projectiveUniversalIncidence K (Fin 4) d ≫ Limits.prod.snd := by
            exact (congrArg (fun g ↦ u i ≫ g)
              (projectiveUniversalIncidence_snd K (Fin 4) d)).symm
      _ = r ≫ projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) marked
          (homogeneousFrameToParameters d e q hqliq) i ≫ Limits.prod.snd := by
            simpa only [Category.assoc] using
              congrArg (fun g ↦ g ≫ Limits.prod.snd) (hu i)
      _ = t ≫ homogeneousFrameToParameters d e q hqliq := by
            dsimp [t]
            exact congrArg (fun g ↦ r ≫ g)
              (projectiveUniversalFiniteIncidenceParameterMap_snd K (Fin 4) d
                (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) marked
                (homogeneousFrameToParameters d e q hqliq) i)
  have huAmbient : ∀ i, u i ≫ projectiveUniversalToAmbient K (Fin 4) d =
      Spec.map (CommRingCat.ofHom f) ≫
        (cubicSurfaceAffinePointLinearNormalizedProjectivePoint cubic hcubic c (E i).1
          (hcommon (E i).1 (E i).2) ≫ hypersurfaceToAmbient cubic hcubic) := by
    intro i
    calc
      u i ≫ projectiveUniversalToAmbient K (Fin 4) d =
          u i ≫ projectiveUniversalIncidence K (Fin 4) d ≫ Limits.prod.fst := by
            exact (congrArg (fun g ↦ u i ≫ g)
              (projectiveUniversalIncidence_fst K (Fin 4) d)).symm
      _ = r ≫ projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) marked
          (homogeneousFrameToParameters d e q hqliq) i ≫ Limits.prod.fst := by
            simpa only [Category.assoc] using
              congrArg (fun g ↦ g ≫ Limits.prod.fst) (hu i)
      _ = r ≫ pullback.fst (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) k).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≫ marked i := by
            exact congrArg (fun g ↦ r ≫ g)
              (projectiveUniversalFiniteIncidenceParameterMap_fst K (Fin 4) d
                (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) k).hom
                (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) marked
                (homogeneousFrameToParameters d e q hqliq) i)
      _ = b i ≫ points i ≫ hypersurfaceToAmbient cubic hcubic := (hb i).symm
      _ = b 0 ≫ points i ≫ hypersurfaceToAmbient cubic hcubic := by rw [hbeq i]
      _ = Spec.map (CommRingCat.ofHom f) ≫ points i ≫
          hypersurfaceToAmbient cubic hcubic := by rw [hf]
      _ = Spec.map (CommRingCat.ofHom f) ≫
          (cubicSurfaceAffinePointLinearNormalizedProjectivePoint cubic hcubic c (E i).1
            (hcommon (E i).1 (E i).2) ≫ hypersurfaceToAmbient cubic hcubic) := by
              rw [hpoints i]
  exact homogeneousFrame_parameterization_universalFamily_points_impossible_of_submodule_evaluation_injective
    f cubic hcubic W qW q hq hqli hqliq hn S hinj c hcommon E e t ht u huBase huAmbient


/-! ## Length-eight incidence avoidance for `leeffective` -/

/-- The eight-point configuration of a prime cubic surface is outside the
finite universal-incidence locus for every independently framed homogeneous
system of dimension at most eight.  This is the geometric genericity input
behind the inequality `h⁰ ≥ 9` in the fixed-component argument. -/
theorem exists_eight_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 8)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)] :
    ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 8
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq) := by
  obtain ⟨S, c, hcommon, E, points, a, hScard, hinj, hdirections,
    hpoints, haBase, haCoordinates⟩ :=
    exists_eight_cubicSurfaceHomogeneousSystem_evaluation_injective_orderedConfigurationFieldPoint
      cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
  exact exists_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_configuration
    cubic hcubic W qW q hq hqli hqliq hn e S hinj c hcommon E points a hpoints haCoordinates

/-- The eleven-point configuration of a prime cubic surface is outside the
finite universal-incidence locus for any independent homogeneous frame whose
span is detected by evaluation on that configuration. -/
theorem exists_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 11)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)] :
    ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 11
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq) := by
  obtain ⟨S, c, hcommon, E, points, a, hScard, hinj, hdirections,
    hpoints, haBase, haCoordinates⟩ :=
    exists_eleven_cubicSurfaceHomogeneousSystem_evaluation_injective_orderedConfigurationFieldPoint
      cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
  exact exists_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_configuration
    cubic hcubic W qW q hq hqli hqliq hn e S hinj c hcommon E points a hpoints haCoordinates

/-- The length-sixteen configuration used to complete a degree-ten datum is
outside every finite universal-incidence locus from an independently framed
homogeneous system that it detects. -/
theorem exists_sixteen_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 16)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)] :
    ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 16
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq) := by
  obtain ⟨S, c, hcommon, E, points, a, hScard, hinj, hdirections,
    hpoints, haBase, haCoordinates⟩ :=
    exists_sixteen_cubicSurfaceHomogeneousSystem_evaluation_injective_orderedConfigurationFieldPoint
      cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
  exact exists_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_configuration
    cubic hcubic W qW q hq hqli hqliq hn e S hinj c hcommon E points a hpoints haCoordinates

/- The empty auxiliary system is enough to turn the sixteen-point evaluator
   theorem into a plain nonemptiness result for the ordered configuration. -/
theorem nonempty_sixteen_cubicOrderedConfiguration_of_prime
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [IsSeparated (hypersurfaceToBase cubic hcubic)] :
    Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left := by
  let W : Submodule K (MvPolynomial (Fin 4) K) := ⊥
  let qW : Fin 0 → W := Fin.elim0
  let q : Fin 0 → homogeneousSubmodule (Fin 4) K 1 := Fin.elim0
  let e : Fin (Fintype.card (Monomials (Fin 4) 1)) ≃ Monomials (Fin 4) 1 :=
    (Fintype.equivFin _).symm
  have hdim : Module.finrank K W ≤ 16 := by
    simp [W]
  have hhom : ∀ z ∈ W, z.IsHomogeneous 1 := by
    intro z hz
    simp only [W, Submodule.mem_bot] at hz
    simpa [hz] using (MvPolynomial.isHomogeneous_zero (Fin 4) K 1)
  have hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0 := by
    intro z hz _
    simpa only [W, Submodule.mem_bot] using hz
  have hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1 := by
    intro j
    exact Fin.elim0 j
  have hqli : LinearIndependent K qW := by
    exact linearIndependent_empty_type
  have hqliq : LinearIndependent K q := by
    exact linearIndependent_empty_type
  have hn : Module.finrank K W = 0 := by
    simp [W]
  obtain ⟨x, _⟩ :=
    exists_sixteen_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
      cubic hcubic hcubic_ne hcubic_prime (by decide : 0 < 1) W hhom hseparate hdim
      qW q hq hqli hqliq hn e
  exact ⟨x⟩

/-! ## Generic length-eight incidence avoidance -/

/-- The generic ordered eight-point configuration of a prime cubic surface
avoids every finite universal-incidence locus coming from a homogeneous
system of dimension at most eight. -/
theorem genericFunctionField_closedPoint_avoids_eight_cubicOrderedConfigurationHomogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 8)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).left] :
    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 8
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq) := by
  apply genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    K (Fin 4) d
    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).hom
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 8
      (hypersurfaceToAmbient cubic hcubic) i)
    (homogeneousFrameToParameters d e q hqliq)
  exact
    exists_eight_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
      cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
        qW q hq hqli hqliq hn e

/-- The generic ordered eleven-point configuration of a prime cubic surface
avoids every finite universal-incidence locus coming from an independently
framed homogeneous system that is detected by the eleven-point evaluator. -/
theorem genericFunctionField_closedPoint_avoids_cubicOrderedConfigurationHomogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 11)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).left] :
    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 11
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq) := by
  apply genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    K (Fin 4) d
    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).hom
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 11
      (hypersurfaceToAmbient cubic hcubic) i)
    (homogeneousFrameToParameters d e q hqliq)
  exact exists_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
    cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim qW q hq hqli hqliq hn e

/-- The generic ordered sixteen-point configuration avoids every finite
universal-incidence locus from an independently framed homogeneous system of
dimension at most sixteen. -/
theorem genericFunctionField_closedPoint_avoids_sixteen_cubicOrderedConfigurationHomogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 16)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left] :
    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 16
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq) := by
  apply genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    K (Fin 4) d
    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 16
      (hypersurfaceToAmbient cubic hcubic) i)
    (homogeneousFrameToParameters d e q hqliq)
  exact exists_sixteen_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
    cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim qW q hq hqli hqliq hn e

/-- The generic sixteen-point configuration admits no nonzero projective
equation from a detected homogeneous frame that vanishes at all marked
points.  It is expressed intrinsically by excluding a common field-valued
parameter and compatible universal-family lifts. -/
theorem not_exists_common_fieldPoints_at_generic_sixteen_cubicOrderedConfigurationHomogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 16)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left] :
    ¬ ∃ (t : Spec (.of (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left.functionField) ⟶
          projectiveLinearSystemParameters (K := K) (τ := Fin n))
      (u : Fin 16 → (Spec (.of (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left.functionField) ⟶
        projectiveUniversalFamily K (Fin 4) d))
      (hbase : (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left.fromSpecStalk
          (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left) ≫
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom =
        t ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))),
      ∀ i, u i ≫ projectiveUniversalIncidence K (Fin 4) d =
        pullback.lift
          ((orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left.fromSpecStalk
            (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left))
          t hbase ≫
          projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
            (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 16
              (hypersurfaceToAmbient cubic hcubic) i)
            (homogeneousFrameToParameters d e q hqliq) i := by
  apply not_exists_common_fieldPoints_at_generic_of_exists
    K (Fin 4) d
    (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 16
      (hypersurfaceToAmbient cubic hcubic) i)
    (homogeneousFrameToParameters d e q hqliq)
  exact exists_sixteen_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
    cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim qW q hq hqli hqliq hn e

end CubicSurfaceFrameRoots

section GenericAvoidance

variable {K : Type u} [Field K] {σ : Type} [Finite σ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The generic-point avoidance theorem applies directly to a family of
equations in the projective span of an independent homogeneous frame. -/
theorem genericFunctionField_closedPoint_avoids_homogeneousFrameIncidence
    {m n : ℕ} {B : Scheme.{u}} [IsIntegral B]
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K))
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (s : B ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (hproper : homogeneousFrameIncidenceParameterMap d a e q hqli s ⁻¹'
      Set.range (projectiveUniversalIncidence K σ d) ≠ Set.univ) :
    B.fromSpecStalk (genericPoint B) (IsLocalRing.closedPoint B.functionField) ∉
      homogeneousFrameIncidenceParameterMap d a e q hqli s ⁻¹'
        Set.range (projectiveUniversalIncidence K σ d) :=
  genericFunctionField_closedPoint_avoids_projectiveUniversalIncidence_preimage
    K σ d (homogeneousFrameIncidenceParameterMap d a e q hqli s) hproper

/-- For a projective system of homogeneous sections, a concrete parameter
value outside the vanishing incidence is enough to make the generic
configuration avoid that incidence.  Properness of the bad locus is derived
from the witness, while its closedness is supplied by the universal
projective incidence construction. -/
theorem genericFunctionField_closedPoint_avoids_homogeneousFrameIncidence_of_exists
    {m n : ℕ} {B : Scheme.{u}} [IsIntegral B]
    (a : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K))
    (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (s : B ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (hgood : ∃ b : B,
      b ∉ homogeneousFrameIncidenceParameterMap d a e q hqli s ⁻¹'
        Set.range (projectiveUniversalIncidence K σ d)) :
    B.fromSpecStalk (genericPoint B) (IsLocalRing.closedPoint B.functionField) ∉
      homogeneousFrameIncidenceParameterMap d a e q hqli s ⁻¹'
        Set.range (projectiveUniversalIncidence K σ d) := by
  apply genericFunctionField_closedPoint_avoids_homogeneousFrameIncidence
    (K := K) (σ := σ) d a e q hqli s
  exact homogeneousFrameIncidence_badLocus_ne_univ_of_exists d a e q hqli s hgood

/-- A proper projective family of equations in a homogeneous frame defines a
closed bad locus on a configuration base: the locus where some equation of
the family vanishes at every marked point.  A witness outside that locus makes
the generic configuration avoid it.  This is the finite-configuration form
of the universal-incidence step used in Voisin's very-general argument. -/
theorem genericFunctionField_closedPoint_avoids_finiteHomogeneousFrameIncidence_of_exists
    {X T : Scheme.{u}} {ι : Type} [IsIntegral X]
    (xBase : X ⟶ Spec (.of K)) (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K)))
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (q : Fin n → homogeneousSubmodule σ K d)
    (hqli : LinearIndependent K q)
    (s : T ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (hgood : ∃ x : X,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K σ d xBase tBase a
        (s ≫ homogeneousFrameToParameters d e q hqli)) :
    X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint X.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K σ d xBase tBase a
        (s ≫ homogeneousFrameToParameters d e q hqli) :=
  genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    K σ d xBase tBase a (s ≫ homogeneousFrameToParameters d e q hqli) hgood

end GenericAvoidance

section CubicConfigurationAvoidance

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On an actual ordered configuration of a cubic hypersurface, the generic
configuration avoids the locus where an equation in a proper projective
system generated by an independent homogeneous frame vanishes at every marked
point, as soon as one witness configuration does.  This is the precise
configuration-space form of the projective-incidence step in Voisin's
very-general argument. -/
theorem genericFunctionField_closedPoint_avoids_cubicOrderedConfigurationHomogeneousFrameIncidence_of_exists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d r : ℕ)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hint : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).left]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    {m n : ℕ} (e : Fin m ≃ Monomials (Fin 4) d)
    (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hqli : LinearIndependent K q)
    (s : T ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (hgood : ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).hom tBase
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r
          (hypersurfaceToAmbient p hp) i)
        (s ≫ homogeneousFrameToParameters d e q hqli)) :
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).hom tBase
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r
          (hypersurfaceToAmbient p hp) i)
        (s ≫ homogeneousFrameToParameters d e q hqli) :=
  @genericFunctionField_closedPoint_avoids_orderedConfigurationProjectiveIncidence_of_exists
    K _ (Fin 4) _ d _ _ _ _ _ (grading (equationIdeal p hp)) _
    (hypersurfaceToBase p hp) hsep r _ hint (hypersurfaceToAmbient p hp) tBase _
    (s ≫ homogeneousFrameToParameters d e q hqli) hgood

/-- The explicit eleven-point configuration on a prime cubic surface lies
outside every simultaneous universal-incidence locus for equations of degree
at most two.  The proof keeps all incidence lifts over one field and one
normalized coefficient chart before invoking the extension-stable quadratic
witness. -/
theorem exists_cubicOrderedConfiguration_point_outside_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) :
    ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
        (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
          (hypersurfaceToAmbient p hp)) s := by
  obtain ⟨S, c, hcommon, e, q, a, hScard, hquad, hsdir,
    hq, haBase, haCoordinates⟩ :=
    exists_eleven_cubicSurfaceQuadraticAvoidance_orderedConfigurationFieldPoint_fieldExtension
      p hp hp0 hprime
  let C := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left
  let marked := @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
    (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
    (hypersurfaceToAmbient p hp)
  let x : C := a (IsLocalRing.closedPoint K)
  refine ⟨x, ?_⟩
  intro hx
  obtain ⟨z, hzfst, hzinc⟩ :=
    exists_parameter_of_mem_projectiveUniversalFiniteIncidenceBadLocus
      K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
      tBase marked s hx
  obtain ⟨L, hL, r, j, u, qj, hrange, hu, hambient, hbaseqj⟩ :=
    exists_common_normalizedForm_fieldPoints_of_mem_all_parameterMap_range
      K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
      tBase marked s z hzinc
  letI : Field L := hL
  let cL : Spec (.of L) := IsLocalRing.closedPoint L
  have hrcL : r cL = z := by
    have hmem : r cL ∈ Set.range r := ⟨cL, rfl⟩
    rw [hrange] at hmem
    simpa only [Set.mem_singleton_iff] using hmem
  have hmarked : ∀ i, a ≫ marked i = q i ≫ hypersurfaceToAmbient p hp := by
    intro i
    unfold marked orderedConfigurationProjectivePoint
    change a ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11) ≫
        Over.Hom.left (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i) ≫
        hypersurfaceToAmbient p hp = _
    simpa only [← Category.assoc] using
      congrArg (fun g ↦ g ≫ hypersurfaceToAmbient p hp) (haCoordinates i)
  have hfactor : ∀ i : Fin 11, ∃ b : Spec (.of L) ⟶ Spec (.of K),
      b ≫ q i ≫ hypersurfaceToAmbient p hp =
        r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
          tBase ≫ marked i := by
    intro i
    rw [hq i]
    apply exists_spec_factor_cubicSurfaceAffinePointLinearNormalizedProjectivePoint_of_mem_ambient_range
      p hp c (e i).1 (hcommon (e i).1 (e i).2)
    refine ⟨IsLocalRing.closedPoint K, ?_⟩
    have hpoint :
        (r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
          tBase ≫ marked i) cL =
          (q i ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint K) := by
      change marked i (pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase (r cL)) = _
      rw [hrcL, hzfst]
      calc
        marked i (a (IsLocalRing.closedPoint K)) =
            (a ≫ marked i) (IsLocalRing.closedPoint K) :=
              (Scheme.Hom.comp_apply _ _ _).symm
        _ = (q i ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint K) := by
              rw [hmarked i]
    simpa only [hq i] using hpoint.symm
  choose b hb using hfactor
  have hbsurface : ∀ i,
      b i ≫ q i =
        ((r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
          tBase) ≫ (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left := by
    intro i
    apply (cancel_mono (hypersurfaceToAmbient p hp)).mp
    calc
      (b i ≫ q i) ≫ hypersurfaceToAmbient p hp = b i ≫ q i ≫
          hypersurfaceToAmbient p hp := Category.assoc _ _ _
      _ = r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
            marked i := hb i
      _ =
          r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left ≫
            hypersurfaceToAmbient p hp := by
              rfl
      _ = (r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left ≫
            hypersurfaceToAmbient p hp := (Category.assoc _ _ _).symm
      _ = ((r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left ≫
            hypersurfaceToAmbient p hp := (Category.assoc _ _ _).symm
      _ = (((r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left) ≫
            hypersurfaceToAmbient p hp := by
              exact (Category.assoc _ _ _).symm
  have hcoordinateBase : ∀ i,
      (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left ≫
          hypersurfaceToBase p hp =
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
    intro i
    change Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11) ≫
      ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left ≫
        hypersurfaceToBase p hp) = _
    rw [orderedFamilyCoordinate_toBase]
    exact (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11).w
  have hcoordinateBaseLeft : ∀ i,
      ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left) ≫
          hypersurfaceToBase p hp =
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
    intro i
    change (Over.Hom.left (orderedFamilyConfigurationι
      (hypersurfaceToBase p hp) 11) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left) ≫
      hypersurfaceToBase p hp = _
    rw [Category.assoc]
    exact hcoordinateBase i
  have hbsurfaceBase : ∀ i,
      (b i ≫ q i) ≫ hypersurfaceToBase p hp =
        (((r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left) ≫
          hypersurfaceToBase p hp := by
    intro i
    exact congrArg (fun g ↦ g ≫ hypersurfaceToBase p hp) (hbsurface i)
  have hbbase : ∀ i,
      b i ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) =
        r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
          tBase ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
    intro i
    calc
      b i ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) =
          (b i ≫ q i) ≫ hypersurfaceToBase p hp := by
            rw [Category.assoc, hq i,
              cubicSurfaceAffinePointLinearNormalizedProjectivePoint_toBase]
      _ = (((r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left) ≫
          hypersurfaceToBase p hp := hbsurfaceBase i
      _ = r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
            calc
              (((r ≫ pullback.fst
                  (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
                  (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
                  (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left) ≫
                  hypersurfaceToBase p hp =
                  (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
                    ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
                      ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left ≫
                        hypersurfaceToBase p hp)) := by
                          calc
                            (((r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                                  tBase) ≫
                                (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
                                (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left) ≫
                                hypersurfaceToBase p hp =
                              ((r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                                  tBase) ≫
                                (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
                                ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left ≫
                                  hypersurfaceToBase p hp) := Category.assoc _ _ _
                            _ = (r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                                  tBase) ≫
                                ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
                                  ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left ≫
                                    hypersurfaceToBase p hp)) := Category.assoc _ _ _
              _ = (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
                    (((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
                      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left) ≫
                      hypersurfaceToBase p hp) := by
                        exact congrArg (fun g ↦
                          (r ≫ pullback.fst
                            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                              tBase) ≫ g) (Category.assoc _ _ _).symm
              _ = _ := by
                exact congrArg (fun g ↦
                  (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                      tBase) ≫ g) (hcoordinateBaseLeft i)
  have hbeq : ∀ i, b i = b 0 := by
    intro i
    have hbbase' : ∀ i, b i = r ≫ pullback.fst
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
      intro i
      simpa only [show CommRingCat.ofHom (RingHom.id K) = 𝟙 _ by rfl,
        Spec.map_id, Category.comp_id] using hbbase i
    exact (hbbase' i).trans (hbbase' 0).symm
  let f : K →+* L := (Spec.preimage (b 0)).hom
  have hf : Spec.map (CommRingCat.ofHom f) = b 0 := Spec.map_preimage _
  let B : ParameterChartRing K (Fin 4) d j →+* L := (Spec.preimage u).hom
  have hB : Spec.map (CommRingCat.ofHom B) = u := Spec.map_preimage _
  let Q : MvPolynomial (Fin 4) L := (normalizedForm K (Fin 4) d j).map B
  have hQhom : Q.IsHomogeneous d :=
    (normalizedForm_isHomogeneous K (Fin 4) d j).map B
  have hroot : ∀ i : Fin 11,
      MvPolynomial.aeval (fun k ↦ f ((e i).1.1 k)) Q = 0 := by
    intro i
    obtain ⟨k, v, g, hv, hgcoordinates, hgambient⟩ :=
      exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint_fieldExtension
        f p hp c (e i).1 (hcommon (e i).1 (e i).2)
    have hqbase : qj i ≫ hypersurfaceToBase
        (normalizedForm K (Fin 4) d j)
          (normalizedForm_isHomogeneous K (Fin 4) d j) =
        Spec.map (CommRingCat.ofHom B) := by
      calc
        _ = u := hbaseqj i
        _ = _ := hB.symm
    have hqambient : qj i ≫ hypersurfaceToAmbient
        (normalizedForm K (Fin 4) d j)
          (normalizedForm_isHomogeneous K (Fin 4) d j) ≫
          ambientCoefficientMap (chartBaseMap (ParameterIdeal K (Fin 4) d) j) =
        Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k)
            (by decide : 0 < 1) := by
      calc
        _ = qj i ≫ normalizedFamilyToAmbient K (Fin 4) d j := rfl
        _ = r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
            marked i := hambient i
        _ = b i ≫ q i ≫ hypersurfaceToAmbient p hp := (hb i).symm
        _ = b 0 ≫ q i ≫ hypersurfaceToAmbient p hp := by rw [hbeq i]
        _ = Spec.map (CommRingCat.ofHom f) ≫ q i ≫
            hypersurfaceToAmbient p hp := by rw [hf]
        _ = Spec.map (CommRingCat.ofHom g) ≫
            Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
              (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k)
              (by decide : 0 < 1) := by
                rw [hq i]
                exact hgambient.symm
    have hzero : MvPolynomial.aeval
        (fun l ↦ g (AllCharacteristics.GradedChart.normalized
          (MvPolynomial.homogeneousSubmodule (Fin 4) K)
          (MvPolynomial.isHomogeneous_X K k) (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l))) Q = 0 := by
      exact AllCharacteristics.HomogeneousProjective.aeval_map_eq_zero_of_ambient_eq
        (chartBaseMap (ParameterIdeal K (Fin 4) d) j)
        (normalizedForm K (Fin 4) d j)
        (normalizedForm_isHomogeneous K (Fin 4) d j) B (qj i) hqbase k g hqambient
    have hzero' : MvPolynomial.aeval
        (fun l ↦ f ((↑(v⁻¹) : K) *
          cubicSurfaceAffinePointNormalizedConeCoordinates c (e i).1.1 l)) Q = 0 := by
      have hcoordinates :
          (fun l ↦ f ((↑(v⁻¹) : K) *
            cubicSurfaceAffinePointNormalizedConeCoordinates c (e i).1.1 l)) =
          fun l ↦ g (AllCharacteristics.GradedChart.normalized
            (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.isHomogeneous_X K k) (MvPolynomial.X l)
            (MvPolynomial.isHomogeneous_X K l)) := by
        funext l
        exact (hgcoordinates l).symm
      rw [hcoordinates]
      exact hzero
    have hscale :
        (fun l ↦ f ((↑(v⁻¹) : K) *
          cubicSurfaceAffinePointNormalizedConeCoordinates c (e i).1.1 l)) =
        f ((↑(v⁻¹) : K) *
          (MvPolynomial.aeval (e i).1.1 (homogeneousLinearForm c))⁻¹) •
          (fun l ↦ f ((e i).1.1 l)) := by
      ext l
      rw [cubicSurfaceAffinePointNormalizedConeCoordinates]
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.map_mul]
      ring
    have hscalarK : (↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i).1.1 (homogeneousLinearForm c))⁻¹ ≠ 0 :=
      mul_ne_zero (Units.ne_zero (v⁻¹))
        (inv_ne_zero (hcommon (e i).1 (e i).2))
    have hscalar : f ((↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i).1.1 (homogeneousLinearForm c))⁻¹) ≠ 0 := by
      intro h
      apply hscalarK
      apply f.injective
      simpa using h
    apply aeval_eq_zero_of_smul_eq_zero_of_isHomogeneous Q hQhom
      (f ((↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i).1.1 (homogeneousLinearForm c))⁻¹)) hscalar
      (fun l ↦ f ((e i).1.1 l))
    rw [← hscale]
    exact hzero'
  have hvan : ∀ y ∈ S, MvPolynomial.aeval (fun k ↦ f (y.1 k)) Q = 0 := by
    intro y hy
    obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
    have hpoint : (e i).1 = y := congrArg Subtype.val hi
    simpa only [hpoint] using hroot i
  have hquadL : ∀ q' : MvPolynomial (Fin 4) L, q'.IsHomogeneous 2 →
      (∀ y ∈ S, MvPolynomial.aeval (fun k ↦ f (y.1 k)) q' = 0) → q' = 0 :=
    hquad f
  have hQzero : Q = 0 :=
    homogeneous_of_le_two_of_quadratic_avoidance S
      (fun y k ↦ f (y.1 k)) hquadL hd Q hQhom hvan
  exact normalizedForm_map_ne_zero K (Fin 4) d j B hQzero

/-- The explicit eleven-point witness makes the generic ordered configuration
avoid every proper finite projective equation system of degree at most two. -/
theorem genericFunctionField_closedPoint_avoids_cubicOrderedConfiguration_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hint : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) :
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
          (hypersurfaceToAmbient p hp) i)
        s := by
  exact @genericFunctionField_closedPoint_avoids_orderedConfigurationProjectiveIncidence_of_exists
    K _ (Fin 4) _ d _ _ _ _ _ (grading (equationIdeal p hp)) _
    (hypersurfaceToBase p hp) hsep 11 _ hint (hypersurfaceToAmbient p hp) tBase _ s
    (exists_cubicOrderedConfiguration_point_outside_lowDegreeFiniteIncidence
      p hp hp0 hprime d hd tBase s)

/-- The finite-incidence condition descends from ordered points to the actual
unordered configuration quotient used for the generic finite subscheme.
Permutation invariance of the locus turns one good ordered configuration into
a good quotient point. -/
theorem genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFiniteIncidenceImage_of_exists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d r : ℕ)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) r).toScheme]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d)
    (hgood : ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).hom tBase
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r
          (hypersurfaceToAmbient p hp) i)
        s) :
    (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) r).toScheme.fromSpecStalk
      (genericPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) r).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) r).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) r ''
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).hom tBase
          (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r
            (hypersurfaceToAmbient p hp) i)
          s := by
  exact @genericFunctionField_closedPoint_avoids_projectiveConfigurationFiniteIncidenceImage_of_exists
    K _ (Fin 4) _ d (CoordinateRing (equationIdeal p hp)) _
    (Submodule K (CoordinateRing (equationIdeal p hp))) _ _
    (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r hlft hint
    _ (hypersurfaceToAmbient p hp) tBase _ s hgood

/-- The eleven-point quadratic witness also gives generic avoidance after
passing from ordered configurations to their actual projective quotient. -/
theorem genericFunctionField_closedPoint_avoids_cubicConfigurationQuotient_lowDegreeFiniteIncidenceImage
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11).toScheme]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) :
    (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 11).toScheme.fromSpecStalk
      (genericPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 11).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 11).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11 ''
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
          (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
            (hypersurfaceToAmbient p hp) i)
          s := by
  exact genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFiniteIncidenceImage_of_exists
    p hp d 11 tBase s
    (exists_cubicOrderedConfiguration_point_outside_lowDegreeFiniteIncidence
      p hp hp0 hprime d hd tBase s)

/-- The quotient-level low-degree avoidance theorem applies in particular to
every projective linear system written in an independent homogeneous frame. -/
theorem genericFunctionField_closedPoint_avoids_cubicConfigurationQuotient_lowDegreeFrameIncidenceImage
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11).toScheme]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    {m n : ℕ} (e : Fin m ≃ Monomials (Fin 4) d)
    (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hqli : LinearIndependent K q)
    (s : T ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n)) :
    (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 11).toScheme.fromSpecStalk
      (genericPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 11).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 11).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 11 ''
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
          (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
            (hypersurfaceToAmbient p hp) i)
          (s ≫ homogeneousFrameToParameters d e q hqli) := by
  exact genericFunctionField_closedPoint_avoids_cubicConfigurationQuotient_lowDegreeFiniteIncidenceImage
    p hp hp0 hprime d hd tBase (s ≫ homogeneousFrameToParameters d e q hqli)

/-- The frame-specialized form of the quotient incidence theorem. -/
theorem genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFrameIncidenceImage_of_exists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d r : ℕ)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) r).toScheme]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    {m n : ℕ} (e : Fin m ≃ Monomials (Fin 4) d)
    (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hqli : LinearIndependent K q)
    (s : T ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (hgood : ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).hom tBase
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r
          (hypersurfaceToAmbient p hp) i)
        (s ≫ homogeneousFrameToParameters d e q hqli)) :
    (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) r).toScheme.fromSpecStalk
      (genericPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) r).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) r).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) r ''
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).hom tBase
          (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r
            (hypersurfaceToAmbient p hp) i)
          (s ≫ homogeneousFrameToParameters d e q hqli) := by
  exact genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFiniteIncidenceImage_of_exists
    p hp d r tBase (s ≫ homogeneousFrameToParameters d e q hqli) hgood

/-- The preceding incidence-avoidance statement is uniform in an arbitrary
family of finite homogeneous frames.  The family can be indexed by divisor
classes: each class supplies its own proper parameter scheme and frame, while
the one generic configuration avoids the image of the bad locus for every
class.  Representing moving divisor systems by such parameter schemes is the
remaining geometric input in Voisin's Lemma 3.3. -/
theorem
    genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFrameIncidenceImage_family_of_exists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d r : ℕ)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) r).toScheme]
    {κ : Sort _} (T : κ → Scheme.{u})
    (tBase : ∀ c, T c ⟶ Spec (.of K)) [∀ c, IsProper (tBase c)]
    (m n : κ → ℕ)
    (e : ∀ c, Fin (m c) ≃ Monomials (Fin 4) d)
    (q : ∀ c, Fin (n c) → homogeneousSubmodule (Fin 4) K d)
    (hqli : ∀ c, LinearIndependent K (q c))
    (s : ∀ c, T c ⟶ projectiveLinearSystemParameters (K := K) (τ := Fin (n c)))
    (hgood : ∀ c, ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).hom (tBase c)
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r
          (hypersurfaceToAmbient p hp) i)
        (s c ≫ homogeneousFrameToParameters d (e c) (q c) (hqli c))) :
    ∀ c,
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) r).toScheme.fromSpecStalk
        (genericPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
            (hypersurfaceToBase p hp) r).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
            (hypersurfaceToBase p hp) r).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) r ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) r).hom (tBase c)
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep r
              (hypersurfaceToAmbient p hp) i)
            (s c ≫ homogeneousFrameToParameters d (e c) (q c) (hqli c)) := by
  intro c
  exact genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFrameIncidenceImage_of_exists
    p hp d r (tBase c) (e c) (q c) (hqli c) (s c) (hgood c)

/-! ## Unordered length-eight incidence avoidance -/

/-- The eight-point interpolation witness descends to the unordered
configuration quotient.  Thus its generic point avoids every finite
universal-incidence family arising from a homogeneous system of dimension at
most eight. -/
theorem
    genericFunctionField_closedPoint_avoids_eight_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 8)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme] :
    (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
      (genericPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 8).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 ''
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 8
            (hypersurfaceToAmbient cubic hcubic) i)
          (homogeneousFrameToParameters d e q hqliq) := by
  simpa only [Category.id_comp] using
    genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFrameIncidenceImage_of_exists
      cubic hcubic d 8
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) e q hqliq (𝟙 _)
      (exists_eight_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
        cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
          qW q hq hqli hqliq hn e)

/-- Exact generic-point consequence used in `leeffective`: if some member of
an independently framed homogeneous system contains the generic unordered
length-eight configuration, then that system has at least nine sections. -/
theorem nine_le_finrank_of_generic_eight_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (hinc :
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
        (genericPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField) ∈
        projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 8 ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).hom
            (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal cubic hcubic)) _
              (hypersurfaceToBase cubic hcubic) hsep 8
              (hypersurfaceToAmbient cubic hcubic) i)
            (homogeneousFrameToParameters d e q hqliq)) :
    9 ≤ Module.finrank K W := by
  by_contra hbound
  have hdim : Module.finrank K W ≤ 8 := by omega
  exact
    (genericFunctionField_closedPoint_avoids_eight_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
      cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
        qW q hq hqli hqliq hn e) hinc

/-- The eleven-point interpolation witness descends to the unordered
configuration quotient for every independently framed homogeneous subsystem
whose evaluations it detects.  This is the quotient-level form usable by the
generic finite subscheme in Voisin's degree-ten construction. -/
theorem
    genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 11)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 11).toScheme]
    : (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 11).toScheme.fromSpecStalk
      (genericPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 11).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 11).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 11 ''
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 11
            (hypersurfaceToAmbient cubic hcubic) i)
          (homogeneousFrameToParameters d e q hqliq) := by
  simpa only [Category.id_comp] using
    genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFrameIncidenceImage_of_exists
      cubic hcubic d 11
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) e q hqliq (𝟙 _)
      (exists_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
        cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim qW q hq hqli hqliq hn e)

/-- The generic unordered length-sixteen cubic-surface configuration avoids
the image of every finite universal-incidence locus from a homogeneous frame
of dimension at most sixteen.  This is the configuration length needed before
the first cubic--cubic residual in the degree-ten construction. -/
theorem
    genericFunctionField_closedPoint_avoids_sixteen_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 16)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    : (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
      (genericPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 16).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 ''
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
          (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 16
            (hypersurfaceToAmbient cubic hcubic) i)
          (homogeneousFrameToParameters d e q hqliq) := by
  simpa only [Category.id_comp] using
    genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFrameIncidenceImage_of_exists
      cubic hcubic d 16
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) e q hqliq (𝟙 _)
      (exists_sixteen_cubicOrderedConfiguration_point_outside_homogeneousFrameFiniteIncidence_of_submodule_evaluation
        cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim qW q hq hqli hqliq hn e)

/-- A finite-dimensional intrinsic system of degree-`d` sections on a cubic
surface can be lifted, framed, and inserted directly into the generic
sixteen-point incidence-avoidance theorem.  Thus the projective polynomial
parameter system retains the original coordinate-ring evaluations. -/
theorem
    genericFunctionField_closedPoint_avoids_sixteen_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m : ℕ} (hd : 0 < d)
    (W : Submodule K
      (grading (equationIdeal cubic hcubic) d)) [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ 16)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    : ∃ (W' : Submodule K (MvPolynomial (Fin 4) K)) (equiv : W ≃ₗ[K] W')
      (qW : Fin (Module.finrank K W) → W')
      (q : Fin (Module.finrank K W) → homogeneousSubmodule (Fin 4) K d)
      (hqliq : LinearIndependent K q),
      (∀ z ∈ W', z.IsHomogeneous d) ∧
      (∀ z ∈ W', z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0) ∧
      (∀ (w : W) (x : cubicSurfaceAffinePoints cubic),
        MvPolynomial.aeval x.1 (equiv w : MvPolynomial (Fin 4) K) =
          cubicSurfaceCoordinatePointEvaluation cubic hcubic w.1 x) ∧
      Module.finrank K W' = Module.finrank K W ∧
      LinearIndependent K qW ∧
      (∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1) ∧
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
        (genericPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 16 ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
            (toBase (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin (Module.finrank K W)) K)))
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 16
              (hypersurfaceToAmbient cubic hcubic) i)
            (homogeneousFrameToParameters d e q hqliq) := by
  obtain ⟨W', equiv, qW, q, hhom, hseparate, heval, hfinrank, hqli, hqliq, hq⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_homogeneousPolynomialFrame cubic hcubic d W
  letI : AddCommGroup W' := inferInstance
  letI : FiniteDimensional K W' := Module.Finite.equiv equiv
  have hbound : Module.finrank K W' ≤ 16 := by
    rw [hfinrank]
    exact hdim
  refine ⟨W', equiv, qW, q, hqliq, hhom, hseparate, heval, hfinrank, hqli, hq, ?_⟩
  exact
    genericFunctionField_closedPoint_avoids_sixteen_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
      cubic hcubic hcubic_ne hcubic_prime hd W' hhom hseparate hbound qW q hq hqli hqliq
      hfinrank e

/- The intrinsic coordinate-ring formulation is uniform in an indexed family
   of systems.  The generic quotient point is shared by every member of the
   family; each intrinsic system is independently lifted to a polynomial
   frame, so no choice of coordinates is part of the family datum. -/
theorem
    genericFunctionField_closedPoint_avoids_sixteen_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence_family
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d) {κ : Sort _}
    (W : ∀ c : κ,
      Submodule K (grading (equationIdeal cubic hcubic) d))
    (hfd : ∀ c : κ, FiniteDimensional K (W c))
    (hdim : ∀ c : κ, Module.finrank K (W c) ≤ 16)
    (m : κ → ℕ)
    (e : ∀ c : κ, Fin (m c) ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme] :
    ∀ c : κ,
      ∃ (W' : Submodule K (MvPolynomial (Fin 4) K)) (equiv : W c ≃ₗ[K] W')
        (qW : Fin (Module.finrank K (W c)) → W')
        (q : Fin (Module.finrank K (W c)) → homogeneousSubmodule (Fin 4) K d)
        (hqliq : LinearIndependent K q),
        (∀ z ∈ W', z.IsHomogeneous d) ∧
        (∀ z ∈ W', z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0) ∧
        (∀ (w : W c) (x : cubicSurfaceAffinePoints cubic),
          MvPolynomial.aeval x.1 (equiv w : MvPolynomial (Fin 4) K) =
            cubicSurfaceCoordinatePointEvaluation cubic hcubic w.1 x) ∧
        Module.finrank K W' = Module.finrank K (W c) ∧
        LinearIndependent K qW ∧
        (∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1) ∧
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint
            (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 16).toScheme)
          (IsLocalRing.closedPoint
            (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 16 ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).hom
            (toBase (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin (Module.finrank K (W c))) K)))
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 16
              (hypersurfaceToAmbient cubic hcubic) i)
            (homogeneousFrameToParameters d (e c) q hqliq) := by
  intro c
  letI : FiniteDimensional K (W c) := hfd c
  exact genericFunctionField_closedPoint_avoids_sixteen_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence
    cubic hcubic hcubic_ne hcubic_prime hd (W c) (hdim c) (e c)

/-! ## Intrinsic length-eight section systems -/

/-- Every intrinsic homogeneous section system of dimension at most eight
can be lifted to a polynomial frame whose universal incidence family misses
the generic unordered length-eight configuration. -/
theorem
    genericFunctionField_closedPoint_avoids_eight_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m : ℕ} (hd : 0 < d)
    (W : Submodule K
      (grading (equationIdeal cubic hcubic) d)) [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ 8)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme] :
    ∃ (W' : Submodule K (MvPolynomial (Fin 4) K)) (equiv : W ≃ₗ[K] W')
      (qW : Fin (Module.finrank K W) → W')
      (q : Fin (Module.finrank K W) → homogeneousSubmodule (Fin 4) K d)
      (hqliq : LinearIndependent K q),
      (∀ z ∈ W', z.IsHomogeneous d) ∧
      (∀ z ∈ W', z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0) ∧
      (∀ (w : W) (x : cubicSurfaceAffinePoints cubic),
        MvPolynomial.aeval x.1 (equiv w : MvPolynomial (Fin 4) K) =
          cubicSurfaceCoordinatePointEvaluation cubic hcubic w.1 x) ∧
      Module.finrank K W' = Module.finrank K W ∧
      LinearIndependent K qW ∧
      (∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1) ∧
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
        (genericPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 8 ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).hom
            (toBase (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin (Module.finrank K W)) K)))
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 8
              (hypersurfaceToAmbient cubic hcubic) i)
            (homogeneousFrameToParameters d e q hqliq) := by
  obtain ⟨W', equiv, qW, q, hhom, hseparate, heval, hfinrank, hqli, hqliq, hq⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_homogeneousPolynomialFrame cubic hcubic d W
  letI : AddCommGroup W' := inferInstance
  letI : FiniteDimensional K W' := Module.Finite.equiv equiv
  have hbound : Module.finrank K W' ≤ 8 := by
    rw [hfinrank]
    exact hdim
  refine ⟨W', equiv, qW, q, hqliq, hhom, hseparate, heval,
    hfinrank, hqli, hq, ?_⟩
  exact
    genericFunctionField_closedPoint_avoids_eight_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
      cubic hcubic hcubic_ne hcubic_prime hd W' hhom hseparate hbound
        qW q hq hqli hqliq hfinrank e

/-- The length-eleven generic configuration has the same direct
coordinate-ring formulation as the length-sixteen completion: every
finite-dimensional intrinsic homogeneous system is lifted to an independent
polynomial frame without changing its evaluations on the cubic surface. -/
theorem
    genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m : ℕ} (hd : 0 < d)
    (W : Submodule K
      (grading (equationIdeal cubic hcubic) d)) [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ 11)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 11).toScheme]
    : ∃ (W' : Submodule K (MvPolynomial (Fin 4) K)) (equiv : W ≃ₗ[K] W')
      (qW : Fin (Module.finrank K W) → W')
      (q : Fin (Module.finrank K W) → homogeneousSubmodule (Fin 4) K d)
      (hqliq : LinearIndependent K q),
      (∀ z ∈ W', z.IsHomogeneous d) ∧
      (∀ z ∈ W', z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0) ∧
      (∀ (w : W) (x : cubicSurfaceAffinePoints cubic),
        MvPolynomial.aeval x.1 (equiv w : MvPolynomial (Fin 4) K) =
          cubicSurfaceCoordinatePointEvaluation cubic hcubic w.1 x) ∧
      Module.finrank K W' = Module.finrank K W ∧
      LinearIndependent K qW ∧
      (∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1) ∧
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 11).toScheme.fromSpecStalk
        (genericPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 11).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 11).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 11 ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).hom
            (toBase (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin (Module.finrank K W)) K)))
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 11
              (hypersurfaceToAmbient cubic hcubic) i)
            (homogeneousFrameToParameters d e q hqliq) := by
  obtain ⟨W', equiv, qW, q, hhom, hseparate, heval, hfinrank, hqli, hqliq, hq⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_homogeneousPolynomialFrame cubic hcubic d W
  letI : AddCommGroup W' := inferInstance
  letI : FiniteDimensional K W' := Module.Finite.equiv equiv
  have hbound : Module.finrank K W' ≤ 11 := by
    rw [hfinrank]
    exact hdim
  refine ⟨W', equiv, qW, q, hqliq, hhom, hseparate, heval, hfinrank, hqli, hq, ?_⟩
  exact
    genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
      cubic hcubic hcubic_ne hcubic_prime hd W' hhom hseparate hbound qW q hq hqli hqliq
      hfinrank e

/- Every bounded intrinsic family can be lifted to independent polynomial frames
   while retaining the generic length-eight incidence-avoidance theorem.  This
   is the uniform interface needed to apply the fixed-component argument to a
   parameter family of moving systems. -/
theorem
    genericFunctionField_closedPoint_avoids_eight_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence_family
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d) {κ : Sort _}
    (W : ∀ c : κ,
      Submodule K (grading (equationIdeal cubic hcubic) d))
    (hfd : ∀ c : κ, FiniteDimensional K (W c))
    (hdim : ∀ c : κ, Module.finrank K (W c) ≤ 8)
    (m : κ → ℕ)
    (e : ∀ c : κ, Fin (m c) ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme] :
    ∀ c : κ,
      ∃ (W' : Submodule K (MvPolynomial (Fin 4) K)) (equiv : W c ≃ₗ[K] W')
        (qW : Fin (Module.finrank K (W c)) → W')
        (q : Fin (Module.finrank K (W c)) → homogeneousSubmodule (Fin 4) K d)
        (hqliq : LinearIndependent K q),
        (∀ z ∈ W', z.IsHomogeneous d) ∧
        (∀ z ∈ W', z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0) ∧
        (∀ (w : W c) (x : cubicSurfaceAffinePoints cubic),
          MvPolynomial.aeval x.1 (equiv w : MvPolynomial (Fin 4) K) =
            cubicSurfaceCoordinatePointEvaluation cubic hcubic w.1 x) ∧
        Module.finrank K W' = Module.finrank K (W c) ∧
        LinearIndependent K qW ∧
        (∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1) ∧
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint
            (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 8).toScheme)
          (IsLocalRing.closedPoint
            (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 8 ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).hom
            (toBase (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin (Module.finrank K (W c))) K)))
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 8
              (hypersurfaceToAmbient cubic hcubic) i)
            (homogeneousFrameToParameters d (e c) q hqliq) := by
  intro c
  letI : FiniteDimensional K (W c) := hfd c
  exact genericFunctionField_closedPoint_avoids_eight_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence
    cubic hcubic hcubic_ne hcubic_prime hd (W c) (hdim c) (e c)


/- The same intrinsic family bridge is available for the eleven-point
   residual configuration.  This keeps the two quotient lengths used by
   Voisin's degree-ten construction on one uniform coordinate-ring API. -/
theorem
    genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence_family
    [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d) {κ : Sort _}
    (W : ∀ c : κ,
      Submodule K (grading (equationIdeal cubic hcubic) d))
    (hfd : ∀ c : κ, FiniteDimensional K (W c))
    (hdim : ∀ c : κ, Module.finrank K (W c) ≤ 11)
    (m : κ → ℕ)
    (e : ∀ c : κ, Fin (m c) ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 11).toScheme] :
    ∀ c : κ,
      ∃ (W' : Submodule K (MvPolynomial (Fin 4) K)) (equiv : W c ≃ₗ[K] W')
        (qW : Fin (Module.finrank K (W c)) → W')
        (q : Fin (Module.finrank K (W c)) → homogeneousSubmodule (Fin 4) K d)
        (hqliq : LinearIndependent K q),
        (∀ z ∈ W', z.IsHomogeneous d) ∧
        (∀ z ∈ W', z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0) ∧
        (∀ (w : W c) (x : cubicSurfaceAffinePoints cubic),
          MvPolynomial.aeval x.1 (equiv w : MvPolynomial (Fin 4) K) =
            cubicSurfaceCoordinatePointEvaluation cubic hcubic w.1 x) ∧
        Module.finrank K W' = Module.finrank K (W c) ∧
        LinearIndependent K qW ∧
        (∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1) ∧
        (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 11).toScheme.fromSpecStalk
          (genericPoint
            (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 11).toScheme)
          (IsLocalRing.closedPoint
            (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 11).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 11 ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 11).hom
            (toBase (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin (Module.finrank K (W c))) K)))
            (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
              (grading (equationIdeal cubic hcubic)) _ (hypersurfaceToBase cubic hcubic) hsep 11
              (hypersurfaceToAmbient cubic hcubic) i)
            (homogeneousFrameToParameters d (e c) q hqliq) := by
  intro c
  letI : FiniteDimensional K (W c) := hfd c
  exact genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientCoordinateSubmoduleFiniteIncidence
    cubic hcubic hcubic_ne hcubic_prime hd (W c) (hdim c) (e c)

/-- The explicit ten-point quadratic-interpolation configuration on a prime cubic surface lies
outside every simultaneous universal-incidence locus for equations of degree
at most two.  The proof keeps all incidence lifts over one field and one
normalized coefficient chart before invoking the extension-stable quadratic
witness. -/
theorem exists_ten_cubicOrderedConfiguration_point_outside_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) :
    ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase
        (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 10
          (hypersurfaceToAmbient p hp)) s := by
  obtain ⟨S, c, hcommon, e, q, a, hScard, hquad,
    hq, haBase, haCoordinates⟩ :=
    exists_ten_cubicSurfaceLowDegreeAvoidance_orderedConfigurationFieldPoint_fieldExtension
      p hp hp0 hprime
  let C := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left
  let marked := @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
    (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 10
    (hypersurfaceToAmbient p hp)
  let x : C := a (IsLocalRing.closedPoint K)
  refine ⟨x, ?_⟩
  intro hx
  obtain ⟨z, hzfst, hzinc⟩ :=
    exists_parameter_of_mem_projectiveUniversalFiniteIncidenceBadLocus
      K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
      tBase marked s hx
  obtain ⟨L, hL, r, j, u, qj, hrange, hu, hambient, hbaseqj⟩ :=
    exists_common_normalizedForm_fieldPoints_of_mem_all_parameterMap_range
      K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
      tBase marked s z hzinc
  letI : Field L := hL
  let cL : Spec (.of L) := IsLocalRing.closedPoint L
  have hrcL : r cL = z := by
    have hmem : r cL ∈ Set.range r := ⟨cL, rfl⟩
    rw [hrange] at hmem
    simpa only [Set.mem_singleton_iff] using hmem
  have hmarked : ∀ i, a ≫ marked i = q i ≫ hypersurfaceToAmbient p hp := by
    intro i
    unfold marked orderedConfigurationProjectivePoint
    change a ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 10) ≫
        Over.Hom.left (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i) ≫
        hypersurfaceToAmbient p hp = _
    simpa only [← Category.assoc] using
      congrArg (fun g ↦ g ≫ hypersurfaceToAmbient p hp) (haCoordinates i)
  have hfactor : ∀ i : Fin 10, ∃ b : Spec (.of L) ⟶ Spec (.of K),
      b ≫ q i ≫ hypersurfaceToAmbient p hp =
        r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
          tBase ≫ marked i := by
    intro i
    rw [hq i]
    apply exists_spec_factor_cubicSurfaceAffinePointLinearNormalizedProjectivePoint_of_mem_ambient_range
      p hp c (e i).1 (hcommon (e i).1 (e i).2)
    refine ⟨IsLocalRing.closedPoint K, ?_⟩
    have hpoint :
        (r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
          tBase ≫ marked i) cL =
          (q i ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint K) := by
      change marked i (pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase (r cL)) = _
      rw [hrcL, hzfst]
      calc
        marked i (a (IsLocalRing.closedPoint K)) =
            (a ≫ marked i) (IsLocalRing.closedPoint K) :=
              (Scheme.Hom.comp_apply _ _ _).symm
        _ = (q i ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint K) := by
              rw [hmarked i]
    simpa only [hq i] using hpoint.symm
  choose b hb using hfactor
  have hbsurface : ∀ i,
      b i ≫ q i =
        ((r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
          tBase) ≫ (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left := by
    intro i
    apply (cancel_mono (hypersurfaceToAmbient p hp)).mp
    calc
      (b i ≫ q i) ≫ hypersurfaceToAmbient p hp = b i ≫ q i ≫
          hypersurfaceToAmbient p hp := Category.assoc _ _ _
      _ = r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase ≫
            marked i := hb i
      _ =
          r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left ≫
            hypersurfaceToAmbient p hp := by
              rfl
      _ = (r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left ≫
            hypersurfaceToAmbient p hp := (Category.assoc _ _ _).symm
      _ = ((r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left ≫
            hypersurfaceToAmbient p hp := (Category.assoc _ _ _).symm
      _ = (((r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left) ≫
            hypersurfaceToAmbient p hp := by
              exact (Category.assoc _ _ _).symm
  have hcoordinateBase : ∀ i,
      (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left ≫
          hypersurfaceToBase p hp =
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom := by
    intro i
    change Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 10) ≫
      ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left ≫
        hypersurfaceToBase p hp) = _
    rw [orderedFamilyCoordinate_toBase]
    exact (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 10).w
  have hcoordinateBaseLeft : ∀ i,
      ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left) ≫
          hypersurfaceToBase p hp =
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom := by
    intro i
    change (Over.Hom.left (orderedFamilyConfigurationι
      (hypersurfaceToBase p hp) 10) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left) ≫
      hypersurfaceToBase p hp = _
    rw [Category.assoc]
    exact hcoordinateBase i
  have hbsurfaceBase : ∀ i,
      (b i ≫ q i) ≫ hypersurfaceToBase p hp =
        (((r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left) ≫
          hypersurfaceToBase p hp := by
    intro i
    exact congrArg (fun g ↦ g ≫ hypersurfaceToBase p hp) (hbsurface i)
  have hbbase : ∀ i,
      b i ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) =
        r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
          tBase ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom := by
    intro i
    calc
      b i ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) =
          (b i ≫ q i) ≫ hypersurfaceToBase p hp := by
            rw [Category.assoc, hq i,
              cubicSurfaceAffinePointLinearNormalizedProjectivePoint_toBase]
      _ = (((r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left) ≫
          hypersurfaceToBase p hp := hbsurfaceBase i
      _ = r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase ≫
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom := by
            calc
              (((r ≫ pullback.fst
                  (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase) ≫
                  (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι) ≫
                  (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left) ≫
                  hypersurfaceToBase p hp =
                  (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase) ≫
                    ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι ≫
                      ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left ≫
                        hypersurfaceToBase p hp)) := by
                          calc
                            (((r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
                                  tBase) ≫
                                (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι) ≫
                                (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left) ≫
                                hypersurfaceToBase p hp =
                              ((r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
                                  tBase) ≫
                                (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι) ≫
                                ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left ≫
                                  hypersurfaceToBase p hp) := Category.assoc _ _ _
                            _ = (r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
                                  tBase) ≫
                                ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι ≫
                                  ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left ≫
                                    hypersurfaceToBase p hp)) := Category.assoc _ _ _
              _ = (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase) ≫
                    (((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 10).ι ≫
                      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 10 i).left) ≫
                      hypersurfaceToBase p hp) := by
                        exact congrArg (fun g ↦
                          (r ≫ pullback.fst
                            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
                              tBase) ≫ g) (Category.assoc _ _ _).symm
              _ = _ := by
                exact congrArg (fun g ↦
                  (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom
                      tBase) ≫ g) (hcoordinateBaseLeft i)
  have hbeq : ∀ i, b i = b 0 := by
    intro i
    have hbbase' : ∀ i, b i = r ≫ pullback.fst
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom := by
      intro i
      simpa only [show CommRingCat.ofHom (RingHom.id K) = 𝟙 _ by rfl,
        Spec.map_id, Category.comp_id] using hbbase i
    exact (hbbase' i).trans (hbbase' 0).symm
  let f : K →+* L := (Spec.preimage (b 0)).hom
  have hf : Spec.map (CommRingCat.ofHom f) = b 0 := Spec.map_preimage _
  let B : ParameterChartRing K (Fin 4) d j →+* L := (Spec.preimage u).hom
  have hB : Spec.map (CommRingCat.ofHom B) = u := Spec.map_preimage _
  let Q : MvPolynomial (Fin 4) L := (normalizedForm K (Fin 4) d j).map B
  have hQhom : Q.IsHomogeneous d :=
    (normalizedForm_isHomogeneous K (Fin 4) d j).map B
  have hroot : ∀ i : Fin 10,
      MvPolynomial.aeval (fun k ↦ f ((e i).1.1 k)) Q = 0 := by
    intro i
    obtain ⟨k, v, g, hv, hgcoordinates, hgambient⟩ :=
      exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint_fieldExtension
        f p hp c (e i).1 (hcommon (e i).1 (e i).2)
    have hqbase : qj i ≫ hypersurfaceToBase
        (normalizedForm K (Fin 4) d j)
          (normalizedForm_isHomogeneous K (Fin 4) d j) =
        Spec.map (CommRingCat.ofHom B) := by
      calc
        _ = u := hbaseqj i
        _ = _ := hB.symm
    have hqambient : qj i ≫ hypersurfaceToAmbient
        (normalizedForm K (Fin 4) d j)
          (normalizedForm_isHomogeneous K (Fin 4) d j) ≫
          ambientCoefficientMap (chartBaseMap (ParameterIdeal K (Fin 4) d) j) =
        Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k)
            (by decide : 0 < 1) := by
      calc
        _ = qj i ≫ normalizedFamilyToAmbient K (Fin 4) d j := rfl
        _ = r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase ≫
            marked i := hambient i
        _ = b i ≫ q i ≫ hypersurfaceToAmbient p hp := (hb i).symm
        _ = b 0 ≫ q i ≫ hypersurfaceToAmbient p hp := by rw [hbeq i]
        _ = Spec.map (CommRingCat.ofHom f) ≫ q i ≫
            hypersurfaceToAmbient p hp := by rw [hf]
        _ = Spec.map (CommRingCat.ofHom g) ≫
            Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
              (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k)
              (by decide : 0 < 1) := by
                rw [hq i]
                exact hgambient.symm
    have hzero : MvPolynomial.aeval
        (fun l ↦ g (AllCharacteristics.GradedChart.normalized
          (MvPolynomial.homogeneousSubmodule (Fin 4) K)
          (MvPolynomial.isHomogeneous_X K k) (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l))) Q = 0 := by
      exact AllCharacteristics.HomogeneousProjective.aeval_map_eq_zero_of_ambient_eq
        (chartBaseMap (ParameterIdeal K (Fin 4) d) j)
        (normalizedForm K (Fin 4) d j)
        (normalizedForm_isHomogeneous K (Fin 4) d j) B (qj i) hqbase k g hqambient
    have hzero' : MvPolynomial.aeval
        (fun l ↦ f ((↑(v⁻¹) : K) *
          cubicSurfaceAffinePointNormalizedConeCoordinates c (e i).1.1 l)) Q = 0 := by
      have hcoordinates :
          (fun l ↦ f ((↑(v⁻¹) : K) *
            cubicSurfaceAffinePointNormalizedConeCoordinates c (e i).1.1 l)) =
          fun l ↦ g (AllCharacteristics.GradedChart.normalized
            (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.isHomogeneous_X K k) (MvPolynomial.X l)
            (MvPolynomial.isHomogeneous_X K l)) := by
        funext l
        exact (hgcoordinates l).symm
      rw [hcoordinates]
      exact hzero
    have hscale :
        (fun l ↦ f ((↑(v⁻¹) : K) *
          cubicSurfaceAffinePointNormalizedConeCoordinates c (e i).1.1 l)) =
        f ((↑(v⁻¹) : K) *
          (MvPolynomial.aeval (e i).1.1 (homogeneousLinearForm c))⁻¹) •
          (fun l ↦ f ((e i).1.1 l)) := by
      ext l
      rw [cubicSurfaceAffinePointNormalizedConeCoordinates]
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.map_mul]
      ring
    have hscalarK : (↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i).1.1 (homogeneousLinearForm c))⁻¹ ≠ 0 :=
      mul_ne_zero (Units.ne_zero (v⁻¹))
        (inv_ne_zero (hcommon (e i).1 (e i).2))
    have hscalar : f ((↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i).1.1 (homogeneousLinearForm c))⁻¹) ≠ 0 := by
      intro h
      apply hscalarK
      apply f.injective
      simpa using h
    apply aeval_eq_zero_of_smul_eq_zero_of_isHomogeneous Q hQhom
      (f ((↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i).1.1 (homogeneousLinearForm c))⁻¹)) hscalar
      (fun l ↦ f ((e i).1.1 l))
    rw [← hscale]
    exact hzero'
  have hvan : ∀ y ∈ S, MvPolynomial.aeval (fun k ↦ f (y.1 k)) Q = 0 := by
    intro y hy
    obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
    have hpoint : (e i).1 = y := congrArg Subtype.val hi
    simpa only [hpoint] using hroot i
  have hQzero : Q = 0 :=
    hquad f hd Q hQhom hvan
  exact normalizedForm_map_ne_zero K (Fin 4) d j B hQzero

/-- The successor coordinates of the explicit eleven-point cubic configuration lie
outside every simultaneous universal-incidence locus for equations of degree at most two. -/
theorem exists_eleven_cubicOrderedConfiguration_successor_point_outside_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) :
    ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
        (fun i : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
          (hypersurfaceToAmbient p hp) i.succ) s := by
  obtain ⟨S, c, hcommon, e, q, a, hquad, hq, haBase, haCoordinates⟩ :=
    exists_eleven_cubicSurfaceSuccessorLowDegreeAvoidance_orderedConfigurationFieldPoint_fieldExtension
      p hp hp0 hprime
  let C := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left
  let marked := fun i : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
    (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
    (hypersurfaceToAmbient p hp) i.succ
  let x : C := a (IsLocalRing.closedPoint K)
  refine ⟨x, ?_⟩
  intro hx
  obtain ⟨z, hzfst, hzinc⟩ :=
    exists_parameter_of_mem_projectiveUniversalFiniteIncidenceBadLocus
      K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
      tBase marked s hx
  obtain ⟨L, hL, r, j, u, qj, hrange, hu, hambient, hbaseqj⟩ :=
    exists_common_normalizedForm_fieldPoints_of_mem_all_parameterMap_range
      K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
      tBase marked s z hzinc
  letI : Field L := hL
  let cL : Spec (.of L) := IsLocalRing.closedPoint L
  have hrcL : r cL = z := by
    have hmem : r cL ∈ Set.range r := ⟨cL, rfl⟩
    rw [hrange] at hmem
    simpa only [Set.mem_singleton_iff] using hmem
  have hmarked : ∀ i, a ≫ marked i = q i.succ ≫ hypersurfaceToAmbient p hp := by
    intro i
    unfold marked orderedConfigurationProjectivePoint
    change a ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11) ≫
        Over.Hom.left (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ) ≫
        hypersurfaceToAmbient p hp = _
    simpa only [← Category.assoc] using
      congrArg (fun g ↦ g ≫ hypersurfaceToAmbient p hp) (haCoordinates i.succ)
  have hfactor : ∀ i : Fin 10, ∃ b : Spec (.of L) ⟶ Spec (.of K),
      b ≫ q i.succ ≫ hypersurfaceToAmbient p hp =
        r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
          tBase ≫ marked i := by
    intro i
    rw [hq i.succ]
    apply exists_spec_factor_cubicSurfaceAffinePointLinearNormalizedProjectivePoint_of_mem_ambient_range
      p hp c (e i.succ).1 (hcommon (e i.succ).1 (e i.succ).2)
    refine ⟨IsLocalRing.closedPoint K, ?_⟩
    have hpoint :
        (r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
          tBase ≫ marked i) cL =
          (q i.succ ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint K) := by
      change marked i (pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase (r cL)) = _
      rw [hrcL, hzfst]
      calc
        marked i (a (IsLocalRing.closedPoint K)) =
            (a ≫ marked i) (IsLocalRing.closedPoint K) :=
              (Scheme.Hom.comp_apply _ _ _).symm
        _ = (q i.succ ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint K) := by
              rw [hmarked i]
    simpa only [hq i.succ] using hpoint.symm
  choose b hb using hfactor
  have hbsurface : ∀ i,
      b i ≫ q i.succ =
        ((r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
          tBase) ≫ (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left := by
    intro i
    apply (cancel_mono (hypersurfaceToAmbient p hp)).mp
    calc
      (b i ≫ q i.succ) ≫ hypersurfaceToAmbient p hp = b i ≫ q i.succ ≫
          hypersurfaceToAmbient p hp := Category.assoc _ _ _
      _ = r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
            marked i := hb i
      _ =
          r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left ≫
            hypersurfaceToAmbient p hp := by
              rfl
      _ = (r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left ≫
            hypersurfaceToAmbient p hp := (Category.assoc _ _ _).symm
      _ = ((r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left ≫
            hypersurfaceToAmbient p hp := (Category.assoc _ _ _).symm
      _ = (((r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
            (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left) ≫
            hypersurfaceToAmbient p hp := by
              exact (Category.assoc _ _ _).symm
  have hcoordinateBase : ∀ i : Fin 10,
      (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left ≫
          hypersurfaceToBase p hp =
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
    intro i
    change Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11) ≫
      ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left ≫
        hypersurfaceToBase p hp) = _
    rw [orderedFamilyCoordinate_toBase]
    exact (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11).w
  have hcoordinateBaseLeft : ∀ i : Fin 10,
      ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left) ≫
          hypersurfaceToBase p hp =
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
    intro i
    change (Over.Hom.left (orderedFamilyConfigurationι
      (hypersurfaceToBase p hp) 11) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left) ≫
      hypersurfaceToBase p hp = _
    rw [Category.assoc]
    exact hcoordinateBase i
  have hbsurfaceBase : ∀ i,
      (b i ≫ q i.succ) ≫ hypersurfaceToBase p hp =
        (((r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left) ≫
          hypersurfaceToBase p hp := by
    intro i
    exact congrArg (fun g ↦ g ≫ hypersurfaceToBase p hp) (hbsurface i)
  have hbbase : ∀ i,
      b i ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) =
        r ≫ pullback.fst (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
          tBase ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
    intro i
    calc
      b i ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) =
          (b i ≫ q i.succ) ≫ hypersurfaceToBase p hp := by
            rw [Category.assoc, hq i.succ,
              cubicSurfaceAffinePointLinearNormalizedProjectivePoint_toBase]
      _ = (((r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left) ≫
          hypersurfaceToBase p hp := hbsurfaceBase i
      _ = r ≫ pullback.fst
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
            calc
              (((r ≫ pullback.fst
                  (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
                  (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
                  (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left) ≫
                  hypersurfaceToBase p hp =
                  (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
                    ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
                      ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left ≫
                        hypersurfaceToBase p hp)) := by
                          calc
                            (((r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                                  tBase) ≫
                                (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
                                (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left) ≫
                                hypersurfaceToBase p hp =
                              ((r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                                  tBase) ≫
                                (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι) ≫
                                ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left ≫
                                  hypersurfaceToBase p hp) := Category.assoc _ _ _
                            _ = (r ≫ pullback.fst
                                (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                                  tBase) ≫
                                ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
                                  ((orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left ≫
                                    hypersurfaceToBase p hp)) := Category.assoc _ _ _
              _ = (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase) ≫
                    (((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
                      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i.succ).left) ≫
                      hypersurfaceToBase p hp) := by
                        exact congrArg (fun g ↦
                          (r ≫ pullback.fst
                            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                              tBase) ≫ g) (Category.assoc _ _ _).symm
              _ = _ := by
                exact congrArg (fun g ↦
                  (r ≫ pullback.fst
                    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
                      tBase) ≫ g) (hcoordinateBaseLeft i)
  have hbeq : ∀ i, b i = b 0 := by
    intro i
    have hbbase' : ∀ i, b i = r ≫ pullback.fst
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom := by
      intro i
      simpa only [show CommRingCat.ofHom (RingHom.id K) = 𝟙 _ by rfl,
        Spec.map_id, Category.comp_id] using hbbase i
    exact (hbbase' i).trans (hbbase' 0).symm
  let f : K →+* L := (Spec.preimage (b 0)).hom
  have hf : Spec.map (CommRingCat.ofHom f) = b 0 := Spec.map_preimage _
  let B : ParameterChartRing K (Fin 4) d j →+* L := (Spec.preimage u).hom
  have hB : Spec.map (CommRingCat.ofHom B) = u := Spec.map_preimage _
  let Q : MvPolynomial (Fin 4) L := (normalizedForm K (Fin 4) d j).map B
  have hQhom : Q.IsHomogeneous d :=
    (normalizedForm_isHomogeneous K (Fin 4) d j).map B
  have hroot : ∀ i : Fin 10,
      MvPolynomial.aeval (fun k ↦ f ((e i.succ).1.1 k)) Q = 0 := by
    intro i
    obtain ⟨k, v, g, hv, hgcoordinates, hgambient⟩ :=
      exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint_fieldExtension
        f p hp c (e i.succ).1 (hcommon (e i.succ).1 (e i.succ).2)
    have hqbase : qj i ≫ hypersurfaceToBase
        (normalizedForm K (Fin 4) d j)
          (normalizedForm_isHomogeneous K (Fin 4) d j) =
        Spec.map (CommRingCat.ofHom B) := by
      calc
        _ = u := hbaseqj i
        _ = _ := hB.symm
    have hqambient : qj i ≫ hypersurfaceToAmbient
        (normalizedForm K (Fin 4) d j)
          (normalizedForm_isHomogeneous K (Fin 4) d j) ≫
          ambientCoefficientMap (chartBaseMap (ParameterIdeal K (Fin 4) d) j) =
        Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k)
            (by decide : 0 < 1) := by
      calc
        _ = qj i ≫ normalizedFamilyToAmbient K (Fin 4) d j := rfl
        _ = r ≫ pullback.fst
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase ≫
            marked i := hambient i
        _ = b i ≫ q i.succ ≫ hypersurfaceToAmbient p hp := (hb i).symm
        _ = b 0 ≫ q i.succ ≫ hypersurfaceToAmbient p hp := by rw [hbeq i]
        _ = Spec.map (CommRingCat.ofHom f) ≫ q i.succ ≫
            hypersurfaceToAmbient p hp := by rw [hf]
        _ = Spec.map (CommRingCat.ofHom g) ≫
            Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
              (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k)
              (by decide : 0 < 1) := by
                rw [hq i.succ]
                exact hgambient.symm
    have hzero : MvPolynomial.aeval
        (fun l ↦ g (AllCharacteristics.GradedChart.normalized
          (MvPolynomial.homogeneousSubmodule (Fin 4) K)
          (MvPolynomial.isHomogeneous_X K k) (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l))) Q = 0 := by
      exact AllCharacteristics.HomogeneousProjective.aeval_map_eq_zero_of_ambient_eq
        (chartBaseMap (ParameterIdeal K (Fin 4) d) j)
        (normalizedForm K (Fin 4) d j)
        (normalizedForm_isHomogeneous K (Fin 4) d j) B (qj i) hqbase k g hqambient
    have hzero' : MvPolynomial.aeval
        (fun l ↦ f ((↑(v⁻¹) : K) *
          cubicSurfaceAffinePointNormalizedConeCoordinates c (e i.succ).1.1 l)) Q = 0 := by
      have hcoordinates :
          (fun l ↦ f ((↑(v⁻¹) : K) *
            cubicSurfaceAffinePointNormalizedConeCoordinates c (e i.succ).1.1 l)) =
          fun l ↦ g (AllCharacteristics.GradedChart.normalized
            (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.isHomogeneous_X K k) (MvPolynomial.X l)
            (MvPolynomial.isHomogeneous_X K l)) := by
        funext l
        exact (hgcoordinates l).symm
      rw [hcoordinates]
      exact hzero
    have hscale :
        (fun l ↦ f ((↑(v⁻¹) : K) *
          cubicSurfaceAffinePointNormalizedConeCoordinates c (e i.succ).1.1 l)) =
        f ((↑(v⁻¹) : K) *
          (MvPolynomial.aeval (e i.succ).1.1 (homogeneousLinearForm c))⁻¹) •
          (fun l ↦ f ((e i.succ).1.1 l)) := by
      ext l
      rw [cubicSurfaceAffinePointNormalizedConeCoordinates]
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.map_mul]
      ring
    have hscalarK : (↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i.succ).1.1 (homogeneousLinearForm c))⁻¹ ≠ 0 :=
      mul_ne_zero (Units.ne_zero (v⁻¹))
        (inv_ne_zero (hcommon (e i.succ).1 (e i.succ).2))
    have hscalar : f ((↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i.succ).1.1 (homogeneousLinearForm c))⁻¹) ≠ 0 := by
      intro h
      apply hscalarK
      apply f.injective
      simpa using h
    apply aeval_eq_zero_of_smul_eq_zero_of_isHomogeneous Q hQhom
      (f ((↑(v⁻¹) : K) *
        (MvPolynomial.aeval (e i.succ).1.1 (homogeneousLinearForm c))⁻¹)) hscalar
      (fun l ↦ f ((e i.succ).1.1 l))
    rw [← hscale]
    exact hzero'
  have hQzero : Q = 0 :=
    hquad f hd Q hQhom hroot
  exact normalizedForm_map_ne_zero K (Fin 4) d j B hQzero


/-- The ten-point quadratic-interpolation witness makes the generic ordered
ten-point configuration avoid every proper projective equation system of
degree at most two. -/
theorem genericFunctionField_closedPoint_avoids_ten_cubicOrderedConfiguration_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hint : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) :
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 10
          (hypersurfaceToAmbient p hp) i)
        s := by
  exact @genericFunctionField_closedPoint_avoids_orderedConfigurationProjectiveIncidence_of_exists
    K _ (Fin 4) _ d _ _ _ _ _ (grading (equationIdeal p hp)) _
    (hypersurfaceToBase p hp) hsep 10 _ hint (hypersurfaceToAmbient p hp) tBase _ s
    (exists_ten_cubicOrderedConfiguration_point_outside_lowDegreeFiniteIncidence
      p hp hp0 hprime d hd tBase s)

/-- The low-degree avoidance for the ten-point interpolation witness descends
to the unordered configuration quotient.  Consequently the actual generic
degree-ten configuration used in Voisin's construction is not contained in
any simultaneous projective system of degree at most two. -/
theorem genericFunctionField_closedPoint_avoids_ten_cubicConfigurationQuotient_lowDegreeFiniteIncidenceImage
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 10).toScheme]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) :
    (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 10).toScheme.fromSpecStalk
      (genericPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 10).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 10).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 10 ''
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).hom tBase
          (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 10
            (hypersurfaceToAmbient p hp) i)
          s := by
  exact genericFunctionField_closedPoint_avoids_cubicConfigurationQuotientFiniteIncidenceImage_of_exists
    p hp d 10 tBase s
    (exists_ten_cubicOrderedConfiguration_point_outside_lowDegreeFiniteIncidence
      p hp hp0 hprime d hd tBase s)

/- The ten-point interpolation witness already proves that the ordered
   distinct-configuration open is nonempty.  This bridge packages that fact
   with the standard geometric-integrality criterion, so callers no longer
   need to install the quotient integrality instance separately. -/
theorem isIntegral_ten_cubicConfigurationQuotientOpen_of_geometricallyIntegral
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [GeometricallyIntegral (toBase (equationIdeal p hp))]
    [Flat (toBase (equationIdeal p hp))]
    [UniversallyOpen (toBase (equationIdeal p hp))]
    [LocallyOfFiniteType (toBase (equationIdeal p hp))]
    [IsSeparated (hypersurfaceToBase p hp)] :
    IsIntegral (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 10).toScheme := by
  letI : Nonempty
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 10).left := by
    change Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left
    let q : MvPolynomial (Fin 4) K := MvPolynomial.X 0
    have hq : q.IsHomogeneous 1 := by
      exact MvPolynomial.isHomogeneous_X K 0
    have hq0 : q ≠ 0 := by
      exact MvPolynomial.X_ne_zero (R := K) 0
    let tBase : Spec (.of K) ⟶ Spec (.of K) := 𝟙 _
    let s : Spec (.of K) ⟶ projectiveParameters K (Fin 4) 1 :=
      projectiveClassifyingMap q hq hq0 (RingHom.id K)
    obtain ⟨x, _⟩ :=
      exists_ten_cubicOrderedConfiguration_point_outside_lowDegreeFiniteIncidence
        p hp hp0 hprime 1 (by decide) tBase s
    exact ⟨x⟩
  change IsIntegral (cubicConfigurationBase p hp 10)
  exact isIntegral_cubicConfigurationBase_of_geometricallyIntegral p hp 10

/- The ordered-space form is the instance consumed by the ten-point generic
   function-field avoidance theorems. -/
theorem isIntegral_ten_cubicOrderedConfiguration_of_geometricallyIntegral
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [GeometricallyIntegral (toBase (equationIdeal p hp))]
    [Flat (toBase (equationIdeal p hp))]
    [UniversallyOpen (toBase (equationIdeal p hp))]
    [LocallyOfFiniteType (toBase (equationIdeal p hp))] :
    IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left := by
  letI : Nonempty
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 10).left := by
    change Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 10).left
    let q : MvPolynomial (Fin 4) K := MvPolynomial.X 0
    have hq : q.IsHomogeneous 1 := by
      exact MvPolynomial.isHomogeneous_X K 0
    have hq0 : q ≠ 0 := by
      exact MvPolynomial.X_ne_zero (R := K) 0
    let tBase : Spec (.of K) ⟶ Spec (.of K) := 𝟙 _
    let s : Spec (.of K) ⟶ projectiveParameters K (Fin 4) 1 :=
      projectiveClassifyingMap q hq hq0 (RingHom.id K)
    obtain ⟨x, _⟩ :=
      exists_ten_cubicOrderedConfiguration_point_outside_lowDegreeFiniteIncidence
        p hp hp0 hprime 1 (by decide) tBase s
    exact ⟨x⟩
  change IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 10).left
  exact isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral
    (toBase (equationIdeal p hp)) 10

/- The corresponding eleven-point quotient is integral for the same reason:
   the successor-point interpolation witness supplies a point of the ordered
   distinct-configuration open, after which the generic geometric-integrality
   criterion applies. -/
theorem isIntegral_eleven_cubicConfigurationQuotientOpen_of_geometricallyIntegral
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [GeometricallyIntegral (toBase (equationIdeal p hp))]
    [Flat (toBase (equationIdeal p hp))]
    [UniversallyOpen (toBase (equationIdeal p hp))]
    [LocallyOfFiniteType (toBase (equationIdeal p hp))]
    [IsSeparated (hypersurfaceToBase p hp)] :
    IsIntegral (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 11).toScheme := by
  letI : Nonempty
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := by
    change Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left
    let q : MvPolynomial (Fin 4) K := MvPolynomial.X 0
    have hq : q.IsHomogeneous 1 := by
      exact MvPolynomial.isHomogeneous_X K 0
    have hq0 : q ≠ 0 := by
      exact MvPolynomial.X_ne_zero (R := K) 0
    let tBase : Spec (.of K) ⟶ Spec (.of K) := 𝟙 _
    let s : Spec (.of K) ⟶ projectiveParameters K (Fin 4) 1 :=
      projectiveClassifyingMap q hq hq0 (RingHom.id K)
    obtain ⟨x, _⟩ :=
      exists_eleven_cubicOrderedConfiguration_successor_point_outside_lowDegreeFiniteIncidence
        p hp hp0 hprime 1 (by decide) tBase s
    exact ⟨x⟩
  change IsIntegral (cubicConfigurationBase p hp 11)
  exact isIntegral_cubicConfigurationBase_of_geometricallyIntegral p hp 11

/- The ordered-space form is the instance consumed by the eleven-point
   generic function-field avoidance theorems. -/
theorem isIntegral_eleven_cubicOrderedConfiguration_of_geometricallyIntegral
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [GeometricallyIntegral (toBase (equationIdeal p hp))]
    [Flat (toBase (equationIdeal p hp))]
    [UniversallyOpen (toBase (equationIdeal p hp))]
    [LocallyOfFiniteType (toBase (equationIdeal p hp))] :
    IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left := by
  letI : Nonempty
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := by
    change Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left
    let q : MvPolynomial (Fin 4) K := MvPolynomial.X 0
    have hq : q.IsHomogeneous 1 := by
      exact MvPolynomial.isHomogeneous_X K 0
    have hq0 : q ≠ 0 := by
      exact MvPolynomial.X_ne_zero (R := K) 0
    let tBase : Spec (.of K) ⟶ Spec (.of K) := 𝟙 _
    let s : Spec (.of K) ⟶ projectiveParameters K (Fin 4) 1 :=
      projectiveClassifyingMap q hq hq0 (RingHom.id K)
    obtain ⟨x, _⟩ :=
      exists_eleven_cubicOrderedConfiguration_successor_point_outside_lowDegreeFiniteIncidence
        p hp hp0 hprime 1 (by decide) tBase s
    exact ⟨x⟩
  change IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left
  exact isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral
    (toBase (equationIdeal p hp)) 11

/- The same internally constructed witness removes the integrality premise for
   the length-sixteen ordered configuration used in the first residual. -/
theorem isIntegral_sixteen_cubicConfigurationQuotientOpen_of_geometricallyIntegral
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [GeometricallyIntegral (toBase (equationIdeal p hp))]
    [Flat (toBase (equationIdeal p hp))]
    [UniversallyOpen (toBase (equationIdeal p hp))]
    [LocallyOfFiniteType (toBase (equationIdeal p hp))]
    [IsSeparated (hypersurfaceToBase p hp)] :
    IsIntegral (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 16).toScheme := by
  letI : Nonempty
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 16).left := by
    change Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
    exact nonempty_sixteen_cubicOrderedConfiguration_of_prime p hp hp0 hprime
  change IsIntegral (cubicConfigurationBase p hp 16)
  exact isIntegral_cubicConfigurationBase_of_geometricallyIntegral p hp 16

/- The ordered-space form is the instance consumed by the generic-point
   avoidance theorems. -/
theorem isIntegral_sixteen_cubicOrderedConfiguration_of_geometricallyIntegral
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [GeometricallyIntegral (toBase (equationIdeal p hp))]
    [Flat (toBase (equationIdeal p hp))]
    [UniversallyOpen (toBase (equationIdeal p hp))]
    [LocallyOfFiniteType (toBase (equationIdeal p hp))] :
    IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left := by
  letI : Nonempty
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 16).left := by
    change Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
    exact nonempty_sixteen_cubicOrderedConfiguration_of_prime p hp hp0 hprime
  change IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 16).left
  exact isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral
    (toBase (equationIdeal p hp)) 16

/-- After deleting coordinate zero, the generic ordered eleven-point cubic
configuration avoids every proper projective equation system of degree at
most two on its ten retained marked points. -/
theorem genericFunctionField_closedPoint_avoids_eleven_cubicOrderedConfiguration_successor_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hint : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) :
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
        (fun i : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
          (hypersurfaceToAmbient p hp) i.succ)
        s := by
  exact genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
    (fun i : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
      (hypersurfaceToAmbient p hp) i.succ) s
    (exists_eleven_cubicOrderedConfiguration_successor_point_outside_lowDegreeFiniteIncidence
      p hp hp0 hprime d hd tBase s)

/-- Permuting the successor-coordinate witness gives a good eleven-point
configuration for the incidence condition obtained by deleting any specified
coordinate. -/
theorem exists_eleven_cubicOrderedConfiguration_delete_point_outside_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) (i : Fin 11) :
    ∃ x : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
        (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
          (hypersurfaceToAmbient p hp) (i.succAbove j)) s := by
  obtain ⟨x, hx⟩ :=
    exists_eleven_cubicOrderedConfiguration_successor_point_outside_lowDegreeFiniteIncidence
      p hp hp0 hprime d hd tBase s
  let g : Equiv.Perm (Fin 11) :=
    (finSuccEquiv' (0 : Fin 11)).trans (finSuccEquiv' i).symm
  have hgsucc : ∀ j : Fin 10, g j.succ = i.succAbove j := by
    intro j
    change (finSuccEquiv' i).symm ((finSuccEquiv' (0 : Fin 11)) j.succ) =
      i.succAbove j
    have hzero : (0 : Fin 11).succAbove j = j.succ := by simp
    rw [← hzero, finSuccEquiv'_succAbove]
    exact finSuccEquiv'_symm_some i j
  have hmaps : Set.MapsTo (configurationRightAction (hypersurfaceToBase p hp) 11 g)
      (projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
        (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
          (hypersurfaceToAmbient p hp) (i.succAbove j)) s)
      (projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
        (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
          (hypersurfaceToAmbient p hp) j.succ) s) := by
    apply mapsTo_projectiveUniversalFiniteIncidenceBadLocus_of_maps
      K (Fin 4) d
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
      (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
        (hypersurfaceToAmbient p hp) (i.succAbove j))
      (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
        (hypersurfaceToAmbient p hp) j.succ)
      s (configurationRightAction (hypersurfaceToBase p hp) 11 g)
    · exact configurationRightAction_toBase (hypersurfaceToBase p hp) 11 g
    · intro j
      unfold orderedConfigurationProjectivePoint
      change (configurationRightAction (hypersurfaceToBase p hp) 11 g ≫
          (orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
          Over.Hom.left (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 j.succ)) ≫
            hypersurfaceToAmbient p hp =
        ((orderedFamilyConfigurationOpen (hypersurfaceToBase p hp) 11).ι ≫
          Over.Hom.left (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 (i.succAbove j))) ≫
            hypersurfaceToAmbient p hp
      have hcoordinate :=
        configurationRightAction_coordinate (hypersurfaceToBase p hp) 11 g j.succ
      rw [hgsucc j] at hcoordinate
      exact congrArg (fun h => h ≫ hypersurfaceToAmbient p hp) hcoordinate
  let y := (configurationRightAction (hypersurfaceToBase p hp) 11 g⁻¹) x
  refine ⟨y, ?_⟩
  intro hy
  have hbad := hmaps hy
  have hgy : configurationRightAction (hypersurfaceToBase p hp) 11 g y = x := by
    change configurationRightAction (hypersurfaceToBase p hp) 11 g
      ((configurationRightAction (hypersurfaceToBase p hp) 11 g⁻¹) x) = x
    rw [← Scheme.Hom.comp_apply, ← configurationRightAction_mul,
      inv_mul_cancel, configurationRightAction_one]
    rfl
  rw [hgy] at hbad
  exact hx hbad

/-- The generic eleven-point cubic configuration satisfies the degree-`≤ 2`
Cayley--Bacharach incidence avoidance condition after deleting any coordinate. -/
theorem genericFunctionField_closedPoint_avoids_eleven_cubicOrderedConfiguration_delete_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hint : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) (i : Fin 11) :
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
        (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
          (hypersurfaceToAmbient p hp) (i.succAbove j)) s := by
  exact genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    K (Fin 4) d (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom tBase
    (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 11
      (hypersurfaceToAmbient p hp) (i.succAbove j)) s
    (exists_eleven_cubicOrderedConfiguration_delete_point_outside_lowDegreeFiniteIncidence
      p hp hp0 hprime d hd tBase s i)

/-- At the generic point of the ordered eleven-point configuration, deleting
any chosen coordinate leaves no common field-valued equation parameter of
degree at most two with universal-incidence lifts through all ten remaining
points. This is the pointwise equation-detection consequence of the proper
incidence avoidance theorem. -/
theorem not_exists_common_fieldPoints_at_generic_eleven_cubicOrderedConfiguration_delete_lowDegreeFiniteIncidence
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (d : ℕ) (hd : d ≤ 2)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hint : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 11).left]
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of K)) [IsProper tBase]
    (s : T ⟶ projectiveParameters K (Fin 4) d) (i : Fin 11) :
    let X := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 11).left
    ¬ ∃ (t : Spec (.of X.functionField) ⟶ T)
      (q : Fin 10 → (Spec (.of X.functionField) ⟶
        projectiveUniversalFamily K (Fin 4) d))
      (hbase : X.fromSpecStalk (genericPoint X) ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom =
          t ≫ tBase),
      ∀ j, q j ≫ projectiveUniversalIncidence K (Fin 4) d =
        pullback.lift (X.fromSpecStalk (genericPoint X)) t hbase ≫
          projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) d
            (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
            tBase
            (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _
              (Fin 4) _ _ _ _ _ (grading (equationIdeal p hp)) _
              (hypersurfaceToBase p hp) hsep 11
              (hypersurfaceToAmbient p hp) (i.succAbove j)) s j := by
  dsimp only
  exact not_exists_common_fieldPoints_at_generic_of_exists
    K (Fin 4) d
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom
    tBase
    (fun j : Fin 10 => @orderedConfigurationProjectivePoint K _
      (Fin 4) _ _ _ _ _ (grading (equationIdeal p hp)) _
      (hypersurfaceToBase p hp) hsep 11
      (hypersurfaceToAmbient p hp) (i.succAbove j))
    s
    (exists_eleven_cubicOrderedConfiguration_delete_point_outside_lowDegreeFiniteIncidence
      p hp hp0 hprime d hd tBase s i)

end CubicConfigurationAvoidance

end PfaffianDescent
