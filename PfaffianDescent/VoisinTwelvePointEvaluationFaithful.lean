import PfaffianDescent.VoisinTwelvePointQuadraticKernel
import PfaffianDescent.QuarticConjugateJets
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import Mathlib.RingTheory.Nullstellensatz
import PfaffianDescent.VoisinSectionRestriction

/-!
# Faithfulness of evaluation on a reduced twelve-point intersection

The key remaining hypothesis is geometric: the affine cone of a transverse
cubic--quadric--quadric intersection consists of the origin and the lines
through twelve specified projective points. Once this coverage and radicality
are known, the Nullstellensatz says that evaluating a homogeneous quadric at
the twelve representatives detects its class modulo the intersection ideal.
-/

namespace PfaffianDescent

open MvPolynomial

section

variable {K : Type*} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [IsAlgClosed K] in
/-- A component of polynomial evaluation in a finite product algebra is
ordinary evaluation at the corresponding coordinate tuple. -/
theorem finite_product_evaluation_apply
    {ι : Type*} [Fintype ι]
    (x : ι → Fin 4 → K) (s : MvPolynomial (Fin 4) K) (i : ι) :
    (s.eval₂ (algebraMap K (ι → K)) (fun j t => x t j)) i =
      MvPolynomial.aeval (x i) s := by
  let f := Pi.evalRingHom (fun _ : ι => K) i
  have hf : f.comp (algebraMap K (ι → K)) = RingHom.id K := by
    ext c
    rfl
  have h := MvPolynomial.hom_eval₂ s (algebraMap K (ι → K)) f
    (fun j t => x t j)
  change (s.eval₂ (algebraMap K (ι → K)) (fun j t => x t j)) i = _
  rw [show
    (s.eval₂ (algebraMap K (ι → K)) (fun j t => x t j)) i =
      f (s.eval₂ (algebraMap K (ι → K)) (fun j t => x t j)) from rfl]
  rw [h, hf]
  rfl

omit [IsAlgClosed K] in
/-- Twelve-point specialization of finite-product evaluation. -/
theorem twelve_point_product_evaluation_apply
    (x : Fin 12 → Fin 4 → K) (s : MvPolynomial (Fin 4) K) (i : Fin 12) :
    (s.eval₂ (algebraMap K (Fin 12 → K)) (fun j t => x t j)) i =
      MvPolynomial.aeval (x i) s :=
  finite_product_evaluation_apply x s i

/-- A positive-degree homogeneous polynomial vanishing at twelve projective
representatives lies in the radical homogeneous ideal when those points
exhaust the affine cone. The degree-two case is used for the pencil kernel;
all degrees are needed to bound the Hilbert function of the intersection. -/
theorem homogeneous_mem_ideal_of_twelve_projective_evaluations_zero
    (I : Ideal (MvPolynomial (Fin 4) K)) (hI : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i)
    (d : ℕ) (hd : 0 < d)
    (s : MvPolynomial (Fin 4) K) (hs : s.IsHomogeneous d)
    (hzero : ∀ i, MvPolynomial.aeval (x i) s = 0) :
    s ∈ I := by
  have hvan : s ∈ MvPolynomial.vanishingIdeal K
      (MvPolynomial.zeroLocus K I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    rcases hcover y hy with h0 | ⟨i, c, hci⟩
    · subst y
      exact aeval_zero_eq_zero_of_homogeneous_pos s hs hd
    · rw [hci, QuarticNet.aeval_smul_of_homogeneous s d hs, hzero i, mul_zero]
  have hrad : s ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) (k := K) I]
    exact hvan
  rwa [hI.radical] at hrad

/-- Degree-two specialization of the all-positive-degree detection theorem. -/
theorem quadratic_mem_ideal_of_twelve_projective_evaluations_zero
    (I : Ideal (MvPolynomial (Fin 4) K)) (hI : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i)
    (s : MvPolynomial (Fin 4) K) (hs : s.IsHomogeneous 2)
    (hzero : ∀ i, MvPolynomial.aeval (x i) s = 0) :
    s ∈ I :=
  homogeneous_mem_ideal_of_twelve_projective_evaluations_zero
    I hI x hcover 2 (by decide) s hs hzero

/-- For a radical cubic--quadric--quadric ideal whose projective zero set
is exactly twelve points, those points detect every quadratic equation
except the two defining quadrics. -/
theorem quadratic_vanishing_at_twelve_eq_defining_quadric_span
    (p q r s : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hs : s.IsHomogeneous 2)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (hrad : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i)
    (hzero : ∀ i, MvPolynomial.aeval (x i) s = 0) :
    ∃ a b : K, s = C a * q + C b * r := by
  apply (quadratic_mem_cubic_two_quadric_ideal_iff_scalar_span
    p q r s hp hq hr hs).mp
  rw [← hI]
  exact quadratic_mem_ideal_of_twelve_projective_evaluations_zero
    I hrad x hcover s hs hzero

/-- Under the same coverage hypothesis, the kernel of quadratic evaluation
at the twelve projective points is exactly the two-quadric scalar span. -/
theorem quadratic_twelve_point_evaluation_kernel_iff
    (p q r s : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hs : s.IsHomogeneous 2)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (hrad : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i) :
    (∀ i, MvPolynomial.aeval (x i) s = 0) ↔
      ∃ a b : K, s = C a * q + C b * r := by
  constructor
  · exact quadratic_vanishing_at_twelve_eq_defining_quadric_span
      p q r s hp hq hr hs I hI hrad x hcover
  · rintro ⟨a, b, rfl⟩ i
    have hqI : q ∈ I := by
      rw [hI]
      exact Ideal.subset_span (by simp)
    have hrI : r ∈ I := by
      rw [hI]
      exact Ideal.subset_span (by simp)
    have hq0 : MvPolynomial.eval (x i) q = 0 := by
      simpa using hpoints i q hqI
    have hr0 : MvPolynomial.eval (x i) r = 0 := by
      simpa using hpoints i r hrI
    simp [hq0, hr0]

omit [IsAlgClosed K] in
/-- The twelve-point quadratic-kernel theorem over an arbitrary field. The
only geometric input is the precise degree-two detection implication;
Nullstellensatz supplies that implication over an algebraically closed field,
while descent may supply it over a function field. -/
theorem quadratic_twelve_point_evaluation_kernel_iff_of_detection
    (p q r s : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hs : s.IsHomogeneous 2)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hdetect : ∀ t : MvPolynomial (Fin 4) K,
      t.IsHomogeneous 2 →
      (∀ i, MvPolynomial.aeval (x i) t = 0) → t ∈ I) :
    (∀ i, MvPolynomial.aeval (x i) s = 0) ↔
      ∃ a b : K, s = C a * q + C b * r := by
  constructor
  · intro hs0
    apply (quadratic_mem_cubic_two_quadric_ideal_iff_scalar_span
      p q r s hp hq hr hs).mp
    rw [← hI]
    exact hdetect s hs hs0
  · rintro ⟨a, b, rfl⟩ i
    have hqI : q ∈ I := by
      rw [hI]
      exact Ideal.subset_span (by simp)
    have hrI : r ∈ I := by
      rw [hI]
      exact Ideal.subset_span (by simp)
    have hq0 : MvPolynomial.eval (x i) q = 0 := by
      simpa using hpoints i q hqI
    have hr0 : MvPolynomial.eval (x i) r = 0 := by
      simpa using hpoints i r hrI
    simp [hq0, hr0]

omit [IsAlgClosed K] in
/-- Arbitrary-field version for the actual quadratic section restriction
map. Detection of degree-two equations is the only extra input. -/
theorem twelve_point_homogeneousSectionRestriction_ker_iff_of_detection
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hdetect : ∀ t : MvPolynomial (Fin 4) K,
      t.IsHomogeneous 2 →
      (∀ i, MvPolynomial.aeval (x i) t = 0) → t ∈ I)
    (s : homogeneousSubmodule (Fin 4) K 2) :
    s ∈ LinearMap.ker
      (homogeneousSectionRestriction (K := K)
        (fun j t => x t j : Fin 4 → Fin 12 → K) 2) ↔
      ∃ a b : K, s.1 = C a * q + C b * r := by
  have hiff := quadratic_twelve_point_evaluation_kernel_iff_of_detection
    p q r s.1 hp hq hr s.2 I hI x hpoints hdetect
  constructor
  · intro hs
    apply hiff.mp
    intro i
    have hi := congrArg (fun f : Fin 12 → K => f i)
      (LinearMap.mem_ker.mp hs)
    simpa only [homogeneousSectionRestriction_apply, Pi.zero_apply,
      twelve_point_product_evaluation_apply] using hi
  · intro hs
    apply LinearMap.mem_ker.mpr
    apply funext
    intro i
    have hi := hiff.mpr hs i
    simpa only [homogeneousSectionRestriction_apply, Pi.zero_apply,
      twelve_point_product_evaluation_apply] using hi

/-- The concrete quadratic section-restriction map into the finite product
algebra `K^12` has kernel exactly the scalar pencil of the defining quadrics. -/
theorem twelve_point_homogeneousSectionRestriction_ker_iff
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (hrad : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i)
    (s : homogeneousSubmodule (Fin 4) K 2) :
    s ∈ LinearMap.ker
      (homogeneousSectionRestriction (K := K)
        (fun j t => x t j : Fin 4 → Fin 12 → K) 2) ↔
      ∃ a b : K, s.1 = C a * q + C b * r := by
  let xp : Fin 4 → Fin 12 → K := fun j t => x t j
  have hiff := quadratic_twelve_point_evaluation_kernel_iff
    p q r s.1 hp hq hr s.2 I hI hrad x hpoints hcover
  constructor
  · intro hs
    apply hiff.mp
    intro i
    have hi := congrArg (fun f : Fin 12 → K => f i)
      (LinearMap.mem_ker.mp hs)
    simpa only [homogeneousSectionRestriction_apply, Pi.zero_apply,
      twelve_point_product_evaluation_apply] using hi
  · intro hs
    apply LinearMap.mem_ker.mpr
    apply funext
    intro i
    have hi := hiff.mpr hs i
    simpa only [homogeneousSectionRestriction_apply, Pi.zero_apply,
      twelve_point_product_evaluation_apply] using hi

omit [IsAlgClosed K] in
/-- The two-dimensional-kernel calculation depends only on an exact
description of the quadratic restriction kernel, over any field. -/
theorem twelve_point_homogeneousSectionRestriction_ker_finrank_eq_two_of_kernel_iff
    (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hqr : LinearIndependent K
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩])
    (x : Fin 12 → Fin 4 → K)
    (hkeriff : ∀ s : homogeneousSubmodule (Fin 4) K 2,
      s ∈ LinearMap.ker
        (homogeneousSectionRestriction (K := K)
          (fun j t => x t j : Fin 4 → Fin 12 → K) 2) ↔
        ∃ a b : K, s.1 = C a * q + C b * r) :
    Module.finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K)
        (fun j t => x t j : Fin 4 → Fin 12 → K) 2)) = 2 := by
  let Q : Fin 2 → homogeneousSubmodule (Fin 4) K 2 :=
    ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩]
  let W := LinearMap.ker
    (homogeneousSectionRestriction (K := K)
      (fun j t => x t j : Fin 4 → Fin 12 → K) 2)
  have hW : W = Submodule.span K (Set.range Q) := by
    apply le_antisymm
    · intro s hs
      obtain ⟨a, b, hab⟩ := (hkeriff s).mp hs
      have hrep : s = a • Q 0 + b • Q 1 := by
        apply Subtype.ext
        simpa [Q, smul_eq_C_mul] using hab
      rw [hrep]
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ a
          (Submodule.subset_span (show Q 0 ∈ Set.range Q from ⟨0, rfl⟩))
      · exact Submodule.smul_mem _ b
          (Submodule.subset_span (show Q 1 ∈ Set.range Q from ⟨1, rfl⟩))
    · apply Submodule.span_le.mpr
      rintro s ⟨i, rfl⟩
      fin_cases i
      · apply (hkeriff (Q 0)).mpr
        refine ⟨1, 0, ?_⟩
        simp [Q]
      · apply (hkeriff (Q 1)).mpr
        refine ⟨0, 1, ?_⟩
        simp [Q]
  rw [show LinearMap.ker
      (homogeneousSectionRestriction (K := K)
        (fun j t => x t j : Fin 4 → Fin 12 → K) 2) = W from rfl,
    hW, finrank_span_eq_card hqr]
  norm_num

omit [IsAlgClosed K] in
/-- Detection of quadratic equations at twelve points gives a
two-dimensional restriction kernel over an arbitrary field. -/
theorem twelve_point_homogeneousSectionRestriction_ker_finrank_eq_two_of_detection
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hqr : LinearIndependent K
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩])
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hdetect : ∀ t : MvPolynomial (Fin 4) K,
      t.IsHomogeneous 2 →
      (∀ i, MvPolynomial.aeval (x i) t = 0) → t ∈ I) :
    Module.finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K)
        (fun j t => x t j : Fin 4 → Fin 12 → K) 2)) = 2 := by
  exact twelve_point_homogeneousSectionRestriction_ker_finrank_eq_two_of_kernel_iff
    q r hq hr hqr x (fun s =>
      twelve_point_homogeneousSectionRestriction_ker_iff_of_detection
        p q r hp hq hr I hI x hpoints hdetect s)

omit [IsAlgClosed K] in
/-- An eight-point split of a twelve-point quadratic restriction with
two-dimensional kernel, valid over any field. -/
theorem twelve_point_exists_eight_split_restriction_surjective_of_kernel_finrank
    (x : Fin 12 → Fin 4 → K)
    (hker : Module.finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K)
        (fun j t => x t j : Fin 4 → Fin 12 → K) 2)) = 2) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := K)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) ∧
      LinearMap.ker
        (homogeneousSectionRestriction (K := K)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) =
        LinearMap.ker
          (homogeneousSectionRestriction (K := K)
            (fun j t => x t j : Fin 4 → Fin 12 → K) 2) := by
  let E := homogeneousSectionRestriction (K := K)
    (fun j t => x t j : Fin 4 → Fin 12 → K) 2
  have hdim : Module.finrank K (homogeneousSubmodule (Fin 4) K 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  obtain ⟨κ, a, inst, ha, hcard, F, hF, hsurj, hkerF⟩ :=
    exists_eight_surjective_coordinates_of_twelve_evaluation_with_two_kernel
      E hdim hker
  letI : Fintype κ := inst
  have hEq : F = homogeneousSectionRestriction (K := K)
      (fun (j : Fin 4) (t : κ) => x (a t) j) 2 := by
    apply LinearMap.ext
    intro s
    apply funext
    intro j
    rw [hF]
    change (s.1.eval₂ (algebraMap K (Fin 12 → K))
      (fun j t => x t j)) (a j) =
      (s.1.eval₂ (algebraMap K (κ → K))
        (fun j t => x (a t) j)) j
    rw [twelve_point_product_evaluation_apply]
    exact (finite_product_evaluation_apply (fun t => x (a t)) s.1 j).symm
  refine ⟨κ, a, inst, ha, hcard, ?_, ?_⟩
  · rw [← hEq]
    exact hsurj
  · rw [← hEq]
    exact hkerF

omit [IsAlgClosed K] in
/-- A quadratic detection certificate at twelve points yields a split
surjective eight-point restriction over the same arbitrary field. -/
theorem twelve_point_exists_eight_split_restriction_surjective_of_detection
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hqr : LinearIndependent K
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩])
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hdetect : ∀ t : MvPolynomial (Fin 4) K,
      t.IsHomogeneous 2 →
      (∀ i, MvPolynomial.aeval (x i) t = 0) → t ∈ I) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := K)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) ∧
      LinearMap.ker
        (homogeneousSectionRestriction (K := K)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) =
        LinearMap.ker
          (homogeneousSectionRestriction (K := K)
            (fun j t => x t j : Fin 4 → Fin 12 → K) 2) := by
  exact twelve_point_exists_eight_split_restriction_surjective_of_kernel_finrank
    x (twelve_point_homogeneousSectionRestriction_ker_finrank_eq_two_of_detection
      p q r hp hq hr hqr I hI x hpoints hdetect)

/-- For independent defining quadrics, the finite-product quadratic
restriction kernel has dimension exactly two. -/
theorem twelve_point_homogeneousSectionRestriction_ker_finrank_eq_two
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hqr : LinearIndependent K
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩])
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (hrad : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i) :
    Module.finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K)
        (fun j t => x t j : Fin 4 → Fin 12 → K) 2)) = 2 := by
  let Q : Fin 2 → homogeneousSubmodule (Fin 4) K 2 :=
    ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩]
  let W := LinearMap.ker
    (homogeneousSectionRestriction (K := K)
      (fun j t => x t j : Fin 4 → Fin 12 → K) 2)
  have hW : W = Submodule.span K (Set.range Q) := by
    apply le_antisymm
    · intro s hs
      obtain ⟨a, b, hab⟩ :=
        (twelve_point_homogeneousSectionRestriction_ker_iff
          p q r hp hq hr I hI hrad x hpoints hcover s).mp hs
      have hrep : s = a • Q 0 + b • Q 1 := by
        apply Subtype.ext
        simpa [Q, smul_eq_C_mul] using hab
      rw [hrep]
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ a
          (Submodule.subset_span (show Q 0 ∈ Set.range Q from ⟨0, rfl⟩))
      · exact Submodule.smul_mem _ b
          (Submodule.subset_span (show Q 1 ∈ Set.range Q from ⟨1, rfl⟩))
    · apply Submodule.span_le.mpr
      rintro s ⟨i, rfl⟩
      fin_cases i
      · apply (twelve_point_homogeneousSectionRestriction_ker_iff
          p q r hp hq hr I hI hrad x hpoints hcover (Q 0)).mpr
        refine ⟨1, 0, ?_⟩
        simp [Q]
      · apply (twelve_point_homogeneousSectionRestriction_ker_iff
          p q r hp hq hr I hI hrad x hpoints hcover (Q 1)).mpr
        refine ⟨0, 1, ?_⟩
        simp [Q]
  rw [show LinearMap.ker
      (homogeneousSectionRestriction (K := K)
        (fun j t => x t j : Fin 4 → Fin 12 → K) 2) = W from rfl,
    hW, finrank_span_eq_card hqr]
  norm_num

/-- For a reduced twelve-point cubic--quadric--quadric intersection, eight of
the twelve point evaluations already realize the full eight-dimensional
quadratic quotient. The geometric hypotheses are explicit inputs. -/
theorem twelve_point_exists_eight_surjective_quadratic_evaluations
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hqr : LinearIndependent K
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩])
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (hrad : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
      ∃ F : homogeneousSubmodule (Fin 4) K 2 →ₗ[K] (κ → K),
        (∀ s j, F s j = MvPolynomial.aeval (x (a j)) s.1) ∧
        Function.Surjective F ∧
        LinearMap.ker F = LinearMap.ker
          (homogeneousSectionRestriction (K := K)
            (fun j t => x t j : Fin 4 → Fin 12 → K) 2) := by
  let E := homogeneousSectionRestriction (K := K)
    (fun j t => x t j : Fin 4 → Fin 12 → K) 2
  have hdim : Module.finrank K (homogeneousSubmodule (Fin 4) K 2) = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  have hker : Module.finrank K (LinearMap.ker E) = 2 :=
    twelve_point_homogeneousSectionRestriction_ker_finrank_eq_two
      p q r hp hq hr hqr I hI hrad x hpoints hcover
  obtain ⟨κ, a, inst, ha, hcard, F, hF, hsurj, hkerF⟩ :=
    exists_eight_surjective_coordinates_of_twelve_evaluation_with_two_kernel
      E hdim hker
  refine ⟨κ, a, inst, ha, hcard, F, ?_, hsurj, hkerF⟩
  intro s j
  rw [hF]
  exact twelve_point_product_evaluation_apply x s.1 (a j)

/-- The eight selected points define the literal restriction to the split
degree-eight coefficient algebra. This is the map used by the residual
construction, rather than an auxiliary linear map with the same values. -/
theorem twelve_point_exists_eight_split_restriction_surjective
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hqr : LinearIndependent K
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩])
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (hrad : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ),
      Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := K)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) ∧
      LinearMap.ker
        (homogeneousSectionRestriction (K := K)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) =
        LinearMap.ker
          (homogeneousSectionRestriction (K := K)
            (fun j t => x t j : Fin 4 → Fin 12 → K) 2) := by
  obtain ⟨κ, a, inst, ha, hcard, F, hF, hsurj, hkerF⟩ :=
    twelve_point_exists_eight_surjective_quadratic_evaluations
      p q r hp hq hr hqr I hI hrad x hpoints hcover
  letI : Fintype κ := inst
  have hEq : F = homogeneousSectionRestriction (K := K)
      (fun (j : Fin 4) (t : κ) => x (a t) j) 2 := by
    apply LinearMap.ext
    intro s
    apply funext
    intro j
    rw [hF]
    exact (finite_product_evaluation_apply (fun t => x (a t)) s.1 j).symm
  refine ⟨κ, a, inst, ha, hcard, ?_, ?_⟩
  · rw [← hEq]
    exact hsurj
  · rw [← hEq]
    exact hkerF

/-- The twelve labeled intersection points split into eight points with
surjective quadratic restriction and four complementary labels. This is the
combinatorial split; a degree-four residual scheme still needs geometric
construction. -/
theorem twelve_point_exists_eight_four_split
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hqr : LinearIndependent K
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩])
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (hrad : I.IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K I)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i) :
    ∃ (κ : Type) (a : κ → Fin 12) (inst : Fintype κ)
      (b : Fin 4 → Fin 12),
      Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
      Function.Injective b ∧ (∀ j k, a j ≠ b k) ∧
      (∀ i : Fin 12, (∃ j, a j = i) ∨ ∃ k, b k = i) ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := K)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) ∧
      LinearMap.ker
        (homogeneousSectionRestriction (K := K)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) =
        LinearMap.ker
          (homogeneousSectionRestriction (K := K)
            (fun j t => x t j : Fin 4 → Fin 12 → K) 2) := by
  obtain ⟨κ, a, inst, ha, hcard, hsurj, hker⟩ :=
    twelve_point_exists_eight_split_restriction_surjective
      p q r hp hq hr hqr I hI hrad x hpoints hcover
  letI : Fintype κ := inst
  obtain ⟨b, hb, hab, hcover'⟩ :=
    exists_complementary_four_coordinates a ha hcard
  exact ⟨κ, a, inst, b, ha, hcard, hb, hab, hcover', hsurj, hker⟩

end

end PfaffianDescent
