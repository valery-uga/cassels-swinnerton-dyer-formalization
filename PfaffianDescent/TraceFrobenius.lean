import PfaffianDescent.AlgebraFrobenius
import PfaffianDescent.AffineFreeModuleBaseChange
import PfaffianDescent.FrobeniusResidualLength
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Separable field extensions as Frobenius algebras

Generic transverse complete intersections in Voisin's construction are
finite separable field schemes.  Their field trace supplies the
nondegenerate multiplication functional required by the residual-length
calculation.
-/

namespace PfaffianDescent
open Module
open CategoryTheory AlgebraicGeometry

section
universe u
variable {K : Type u} [Field K]

section FiniteAlgebra

variable {A : Type u} [CommRing A] [Algebra K A]
  [FiniteDimensional K A]

/-- A nondegenerate algebra trace pairing identifies a finite algebra with
its ground-field linear dual.  Stating the construction at this generality
lets the finite-etale coordinate algebra of a disconnected zero-scheme use
the same endpoint as a residue field. -/
noncomputable def finiteAlgebraTraceDualEquiv
    (htrace : (Algebra.traceForm K A).Nondegenerate) :
    A ≃ₗ[K] Module.Dual K A :=
  (Algebra.traceForm K A).toDual htrace

@[simp]
theorem finiteAlgebraTraceDualEquiv_apply
    (htrace : (Algebra.traceForm K A).Nondegenerate) (a x : A) :
    finiteAlgebraTraceDualEquiv htrace a x =
      Algebra.trace K A (a * x) := by
  rw [finiteAlgebraTraceDualEquiv, LinearMap.BilinForm.toDual_def,
    Algebra.traceForm_apply]

/-- Trace duality in terms of global functions on the affine finite algebra
scheme.  This is the linear target used for a finite-etale quotient sheaf. -/
noncomputable def finiteAffineGlobalFunctionsTraceDualEquiv
    (htrace : (Algebra.traceForm K A).Nondegenerate) :
    let p : Spec (.of A) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    letI := Module.compHom Γ(Spec (.of A), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    A ≃ₗ[K] Module.Dual K Γ(Spec (.of A), ⊤) := by
  let p : Spec (.of A) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  letI := Module.compHom Γ(Spec (.of A), ⊤)
    (schemeOpenBaseRingHom p ⊤)
  exact (finiteAlgebraTraceDualEquiv htrace).trans
    (specGlobalFunctionsLinearEquiv K A).dualMap

@[simp]
theorem finiteAffineGlobalFunctionsTraceDualEquiv_apply
    (htrace : (Algebra.traceForm K A).Nondegenerate) (a : A) :
    let p : Spec (.of A) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    letI := Module.compHom Γ(Spec (.of A), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    ∀ s : Γ(Spec (.of A), ⊤),
      finiteAffineGlobalFunctionsTraceDualEquiv htrace a s =
        Algebra.trace K A
          (a * specGlobalFunctionsLinearEquiv K A s) := by
  dsimp
  let p : Spec (.of A) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  letI := Module.compHom Γ(Spec (.of A), ⊤)
    (schemeOpenBaseRingHom p ⊤)
  intro s
  rw [finiteAffineGlobalFunctionsTraceDualEquiv,
    LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    finiteAlgebraTraceDualEquiv_apply]

end FiniteAlgebra

section Product

variable {S T : Type u} [CommRing S] [CommRing T]
  [Algebra K S] [Algebra K T]
  [FiniteDimensional K S] [FiniteDimensional K T]

/-- Nondegeneracy of the trace form is preserved by a binary product of
finite algebras.  Iterating this lemma is the algebraic core of the
finite-etale trace-duality endpoint for a disconnected zero-scheme. -/
theorem traceForm_prod_nondegenerate
    (hS : (Algebra.traceForm K S).Nondegenerate)
    (hT : (Algebra.traceForm K T).Nondegenerate) :
    (Algebra.traceForm K (S × T)).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hS.1 x.1
      intro y
      have h := hx (y, 0)
      simpa [Algebra.traceForm_apply, Algebra.trace_prod_apply] using h
    · apply hT.1 x.2
      intro y
      have h := hx (0, y)
      simpa [Algebra.traceForm_apply, Algebra.trace_prod_apply] using h
  · intro x hx
    apply Prod.ext
    · apply hS.2 x.1
      intro y
      have h := hx (y, 0)
      simpa [Algebra.traceForm_apply, Algebra.trace_prod_apply] using h
    · apply hT.2 x.2
      intro y
      have h := hx (0, y)
      simpa [Algebra.traceForm_apply, Algebra.trace_prod_apply] using h

/-- In particular, the product of two finite separable field extensions has
a nondegenerate trace form.  This is the trace-duality input for a disjoint
union of two closed etale points. -/
theorem traceForm_prod_separable_fields_nondegenerate
    {L₁ L₂ : Type u} [Field L₁] [Field L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [Algebra.IsSeparable K L₁] [Algebra.IsSeparable K L₂] :
    (Algebra.traceForm K (L₁ × L₂)).Nondegenerate :=
  traceForm_prod_nondegenerate
    (traceForm_nondegenerate K L₁)
    (traceForm_nondegenerate K L₂)

end Product

section Transport

variable {A B : Type u} [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  [FiniteDimensional K A] [FiniteDimensional K B]

/-- Nondegeneracy of the algebra trace form transports across an algebra
equivalence. -/
theorem traceForm_nondegenerate_of_algEquiv
    (e : A ≃ₐ[K] B)
    (hB : (Algebra.traceForm K B).Nondegenerate) :
    (Algebra.traceForm K A).Nondegenerate := by
  constructor
  · intro x hx
    apply e.injective
    have he : e x = 0 := hB.1 (e x) (by
      intro y
      have h := hx (e.symm y)
      change Algebra.trace K A (x * e.symm y) = 0 at h
      rw [← Algebra.trace_eq_of_algEquiv e] at h
      simpa using h)
    simpa using he
  · intro x hx
    apply e.injective
    have he : e x = 0 := hB.2 (e x) (by
      intro y
      have h := hx (e.symm y)
      change Algebra.trace K A (e.symm y * x) = 0 at h
      rw [← Algebra.trace_eq_of_algEquiv e] at h
      simpa using h)
    simpa using he

end Transport

section FiniteProducts

/-- Split a dependent product indexed by `Fin (n+1)` into its zeroth factor
and the product of the remaining factors, as an algebra equivalence. -/
noncomputable def piFinSuccAlgEquiv
    (L : Fin (n + 1) → Type u)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)] :
    (∀ i, L i) ≃ₐ[K] L 0 × (∀ j : Fin n, L j.succ) := by
  let f : (∀ i, L i) →ₐ[K] L 0 × (∀ j : Fin n, L j.succ) :=
    AlgHom.prod (Pi.evalAlgHom K L 0)
      (AlgHom.pi fun j : Fin n => Pi.evalAlgHom K L j.succ)
  apply AlgEquiv.ofBijective f
  constructor
  · intro a b hab
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg Prod.fst hab
    · exact congrArg (fun z => z.2 j) hab
  · intro z
    refine ⟨Fin.cases z.1 z.2, ?_⟩
    apply Prod.ext
    · rfl
    · funext j
      rfl

/-- A finite product of finite separable field extensions has nondegenerate
algebra trace form.  This supplies trace duality for an arbitrary split
finite-etale zero-scheme, not only for one or two connected components. -/
theorem traceForm_pi_fin_separable_fields_nondegenerate
    (n : ℕ) (L : Fin n → Type u)
    [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    [∀ i, Algebra.IsSeparable K (L i)] :
    (Algebra.traceForm K (∀ i, L i)).Nondegenerate := by
  induction n with
  | zero =>
      constructor <;> intro x _ <;> exact Subsingleton.elim x 0
  | succ n ih =>
      apply traceForm_nondegenerate_of_algEquiv (piFinSuccAlgEquiv (K := K) L)
      apply traceForm_prod_nondegenerate
      · exact traceForm_nondegenerate K (L 0)
      · exact ih (fun j : Fin n => L j.succ)

/-- The algebra trace on a product indexed by `Fin n` is the sum of the
traces on its factors.  This is the componentwise formula needed to compare
the global trace pairing with the local residue pairings. -/
theorem trace_piFin_apply
    (n : ℕ) (L : Fin n → Type u)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (x : ∀ i, L i) :
    Algebra.trace K (∀ i, L i) x =
      ∑ i, Algebra.trace K (L i) (x i) := by
  induction n with
  | zero =>
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, map_zero]
      simp
  | succ n ih =>
      let e := piFinSuccAlgEquiv (K := K) L
      rw [← Algebra.trace_eq_of_algEquiv e x]
      rw [Algebra.trace_prod_apply]
      rw [ih]
      rw [Fin.sum_univ_succ]
      rfl

/-- The algebra trace on an arbitrary finite dependent product is the sum
of the factor traces. -/
theorem trace_pi_apply
    {I : Type u} [Fintype I] (L : I → Type u)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (x : ∀ i, L i) :
    Algebra.trace K (∀ i, L i) x =
      ∑ i, Algebra.trace K (L i) (x i) := by
  let σ : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let e := AlgEquiv.piCongrLeft K L σ
  calc
    Algebra.trace K (∀ i, L i) x =
        Algebra.trace K (∀ j, L (σ j)) (e.symm x) := by
          simpa [e] using Algebra.trace_eq_of_algEquiv e (e.symm x)
    _ = ∑ j, Algebra.trace K (L (σ j)) ((e.symm x) j) :=
      trace_piFin_apply _ _ _
    _ = ∑ i, Algebra.trace K (L i) (x i) := by
      rw [← σ.sum_comp]
      rfl

/-- Transporting a finite algebra to a product presentation identifies its
trace with the sum of the traces of the displayed components. -/
theorem trace_eq_sum_components_of_algEquiv
    {A I : Type u} [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Fintype I]
    (L : I → Type u)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (e : A ≃ₐ[K] (∀ i, L i)) (a : A) :
    Algebra.trace K A a =
      ∑ i, Algebra.trace K (L i) (e a i) := by
  rw [← Algebra.trace_eq_of_algEquiv e]
  exact trace_pi_apply L (e a)

/-- Under a product presentation, the trace pairing is the sum of the local
trace pairings component by component. -/
theorem trace_mul_eq_sum_components_of_algEquiv
    {A I : Type u} [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Fintype I]
    (L : I → Type u)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (e : A ≃ₐ[K] (∀ i, L i)) (a b : A) :
    Algebra.trace K A (a * b) =
      ∑ i, Algebra.trace K (L i) (e a i * e b i) := by
  rw [trace_eq_sum_components_of_algEquiv L e]
  simp only [map_mul, Pi.mul_apply]

end FiniteProducts

section FiniteEtale

variable {A : Type u} [CommRing A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.Etale K A]

/-- The trace form of any finite etale algebra over a field is
nondegenerate.  The proof decomposes the algebra into its finitely many
separable field factors and transports the product trace pairing back across
the resulting algebra equivalence. -/
theorem traceForm_etale_nondegenerate :
    (Algebra.traceForm K A).Nondegenerate := by
  classical
  obtain ⟨I, hI, Ai, hfield, halgebra, e, hfinite⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  letI : Finite I := hI
  letI : Fintype I := Fintype.ofFinite I
  letI : ∀ i, Field (Ai i) := hfield
  letI : ∀ i, Algebra K (Ai i) := halgebra
  letI : ∀ i, FiniteDimensional K (Ai i) := fun i => (hfinite i).1
  letI : ∀ i, Algebra.IsSeparable K (Ai i) := fun i => (hfinite i).2
  let σ : Fin (Fintype.card I) ≃ I :=
    (Trunc.out (Fintype.truncEquivFin I)).symm
  let e' : A ≃ₐ[K] (∀ j : Fin (Fintype.card I), Ai (σ j)) :=
    e.trans (AlgEquiv.piCongrLeft K Ai σ).symm
  exact traceForm_nondegenerate_of_algEquiv e'
    (traceForm_pi_fin_separable_fields_nondegenerate
      (K := K) (Fintype.card I) (fun j => Ai (σ j)))

end FiniteEtale

variable {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The field trace, regarded as a linear functional. -/
noncomputable abbrev fieldTraceFunctional : Module.Dual K L := Algebra.trace K L

/-- The trace pairing identifies a finite separable field extension with
its linear dual.  This generic form is shared by the residual-intersection
and finite-support Serre-duality arguments. -/
noncomputable def fieldTraceDualEquiv : L ≃ₗ[K] Module.Dual K L :=
  finiteAlgebraTraceDualEquiv (traceForm_nondegenerate K L)

@[simp]
theorem fieldTraceDualEquiv_apply (a x : L) :
    fieldTraceDualEquiv (K := K) (L := L) a x =
      Algebra.trace K L (a * x) := by
  exact finiteAlgebraTraceDualEquiv_apply
    (traceForm_nondegenerate K L) a x

/-- Trace duality written with the intrinsic global functions on the affine
field point `Spec L`.  This is the quotient-side linear target occurring in
Voisin's finite-support Serre-duality comparison. -/
noncomputable def fieldPointGlobalFunctionsTraceDualEquiv :
    let p : Spec (.of L) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K L))
    letI := Module.compHom Γ(Spec (.of L), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    L ≃ₗ[K] Module.Dual K Γ(Spec (.of L), ⊤) := by
  let p : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI := Module.compHom Γ(Spec (.of L), ⊤)
    (schemeOpenBaseRingHom p ⊤)
  exact finiteAffineGlobalFunctionsTraceDualEquiv
    (traceForm_nondegenerate K L)

@[simp]
theorem fieldPointGlobalFunctionsTraceDualEquiv_apply
    (a : L) :
    let p : Spec (.of L) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K L))
    letI := Module.compHom Γ(Spec (.of L), ⊤)
      (schemeOpenBaseRingHom p ⊤)
    ∀ s : Γ(Spec (.of L), ⊤),
      fieldPointGlobalFunctionsTraceDualEquiv (K := K) (L := L) a s =
        Algebra.trace K L
          (a * specGlobalFunctionsLinearEquiv K L s) := by
  dsimp
  let p : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI := Module.compHom Γ(Spec (.of L), ⊤)
    (schemeOpenBaseRingHom p ⊤)
  intro s
  exact finiteAffineGlobalFunctionsTraceDualEquiv_apply
    (traceForm_nondegenerate K L) a s

/-- Separability makes the trace multiplication pairing nondegenerate, hence
the trace is a Frobenius functional in the form used by the residual algebra
API. -/
theorem fieldTraceFunctional_isFrobenius :
    IsFrobeniusFunctional (fieldTraceFunctional (K := K) (L := L)) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate K L).1 (a - b)
  intro x
  have hx := LinearMap.congr_fun hab x
  change Algebra.trace K L (a * x) = Algebra.trace K L (b * x) at hx
  rw [Algebra.traceForm_apply, sub_mul, map_sub, hx, sub_self]

/-- For a finite separable field scheme, the trace pairing gives the
complementary length of every annihilator residual without an additional
Gorenstein hypothesis. -/
theorem residual_quotient_finrank_complement_fieldTrace
    (P : Ideal L) (N d : ℕ) (hL : finrank K L = N)
    (hZ : finrank K (L ⧸ P) = d) :
    finrank K (L ⧸ residualAlgebraIdeal P) = N - d :=
  residual_quotient_finrank_complement fieldTraceFunctional
    fieldTraceFunctional_isFrobenius P N d hL hZ

end
end PfaffianDescent
